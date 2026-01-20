const fs = require("fs");
const path = require("path");
const { execSync } = require("child_process");

function hasCmd(cmd) {
  try {
    execSync(`${cmd} --version`, { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
}

function sh(cmd) {
  // Avoid extremely verbose snarkjs debug logs if DEBUG is set globally.
  execSync(cmd, { stdio: "inherit", env: { ...process.env, DEBUG: "" } });
}

function shOut(cmd) {
  return execSync(cmd, { encoding: "utf8" });
}

function ensureDir(p) {
  fs.mkdirSync(p, { recursive: true });
}

function safeRm(p) {
  try {
    fs.rmSync(p, { force: true });
  } catch {}
}

function findNodeModulesDir(startDir) {
  let cur = startDir;
  for (let i = 0; i < 8; i++) {
    const cand = path.join(cur, "node_modules");
    if (fs.existsSync(cand)) return cand;
    const parent = path.dirname(cur);
    if (parent === cur) break;
    cur = parent;
  }
  return null;
}

function getR1csConstraints(r1csPath) {
  try {
    const out = shOut(`npx snarkjs r1cs info ${r1csPath}`);
    const m =
      out.match(/constraints:\s*(\d+)/i) ||
      out.match(/#\s*of\s*constraints:\s*(\d+)/i) ||
      out.match(/nconstraints:\s*(\d+)/i);
    if (!m) return null;
    return Number(m[1]);
  } catch {
    return null;
  }
}

function choosePtauPower(constraints) {
  if (!constraints || !Number.isFinite(constraints) || constraints <= 0) return 14;
  // Prefer the smallest safe ceremony size; `constraints` is the primary driver.
  // For our circuits, `2^power >= constraints` is sufficient and avoids very slow PTau generation.
  const needed = Math.ceil(Math.log2(constraints + 1));
  return Math.max(12, Math.min(20, needed));
}

function ensurePtau(ptauPath, power) {
  if (fs.existsSync(ptauPath)) {
    try {
      sh(`npx snarkjs powersoftau verify ${ptauPath}`);
      return;
    } catch {
      fs.rmSync(ptauPath, { force: true });
    }
  }

  const dir = path.dirname(ptauPath);
  const p0 = path.join(dir, `pot${power}_0000.ptau`);
  const p1 = path.join(dir, `pot${power}_0001.ptau`);

  sh(`npx snarkjs powersoftau new bn128 ${power} ${p0}`);
  sh(`npx snarkjs powersoftau contribute ${p0} ${p1} --name="HeytingLean dev" -e="heytinglean"`);
  sh(`npx snarkjs powersoftau prepare phase2 ${p1} ${ptauPath}`);

  safeRm(p0);
  safeRm(p1);
}

function rewriteContractName(inPath, outPath, contractName) {
  const src = fs.readFileSync(inPath, "utf8");
  const out = src.replace(/contract\s+Groth16Verifier\s*\{/g, `contract ${contractName} {`);
  fs.writeFileSync(outPath, out);
}

function buildOne({
  circuitPath,
  r1csPath,
  zkeyPrefix,
  vkPath,
  generatedSolTmp,
  generatedSolOut,
  contractName,
  ptauPath,
}) {
  const zkey0 = `${zkeyPrefix}_0000.zkey`;
  const zkey = `${zkeyPrefix}_final.zkey`;
  const force = process.env.FORCE === "1";

  if (!force && fs.existsSync(zkey) && fs.existsSync(vkPath) && fs.existsSync(generatedSolOut)) {
    return;
  }

  safeRm(zkey0);
  safeRm(zkey);
  safeRm(vkPath);
  safeRm(generatedSolTmp);

  sh(`npx snarkjs groth16 setup ${r1csPath} ${ptauPath} ${zkey0}`);
  sh(
    `npx snarkjs zkey contribute ${zkey0} ${zkey} --name="HeytingLean dev" -e="heytinglean"`,
  );
  sh(`npx snarkjs zkey export verificationkey ${zkey} ${vkPath}`);
  sh(`npx snarkjs zkey export solidityverifier ${zkey} ${generatedSolTmp}`);

  rewriteContractName(generatedSolTmp, generatedSolOut, contractName);
}

function main() {
  const ROOT = process.cwd();
  const CIRCUITS_DIR = path.join(ROOT, "circuits");
  const BUILD_DIR = path.join(CIRCUITS_DIR, "build");
  const CONTRACTS_ZK_DIR = path.join(ROOT, "contracts", "zk");

  if (!hasCmd("circom")) {
    throw new Error(
      "circom is required but not installed (expected circom v2.1.x).",
    );
  }

  const nodeModules = findNodeModulesDir(ROOT);
  if (!nodeModules) throw new Error("Could not locate node_modules/ (run npm install at repo root)");

  ensureDir(BUILD_DIR);
  ensureDir(CONTRACTS_ZK_DIR);

  const withdrawCircuit = path.join(CIRCUITS_DIR, "bermudaWithdrawCompliance.circom");
  const depositCircuit = path.join(CIRCUITS_DIR, "bermudaNoteDeposit.circom");

  sh(`circom ${withdrawCircuit} --r1cs --wasm --sym -o ${BUILD_DIR} -l ${nodeModules}`);
  sh(`circom ${depositCircuit} --r1cs --wasm --sym -o ${BUILD_DIR} -l ${nodeModules}`);

  const withdrawR1cs = path.join(BUILD_DIR, "bermudaWithdrawCompliance.r1cs");
  const depositR1cs = path.join(BUILD_DIR, "bermudaNoteDeposit.r1cs");

  const cWithdraw = getR1csConstraints(withdrawR1cs);
  const cDeposit = getR1csConstraints(depositR1cs);

  const pow = Math.max(choosePtauPower(cWithdraw), choosePtauPower(cDeposit));
  const ptau = path.join(BUILD_DIR, `pot${pow}_final.ptau`);
  ensurePtau(ptau, pow);

  buildOne({
    circuitPath: withdrawCircuit,
    r1csPath: withdrawR1cs,
    zkeyPrefix: path.join(BUILD_DIR, "withdraw"),
    vkPath: path.join(BUILD_DIR, "withdraw_verification_key.json"),
    generatedSolTmp: path.join(BUILD_DIR, "withdraw_verifier_tmp.sol"),
    generatedSolOut: path.join(CONTRACTS_ZK_DIR, "GeneratedWithdrawVerifier.sol"),
    contractName: "BermudaWithdrawGroth16Verifier",
    ptauPath: ptau,
  });

  buildOne({
    circuitPath: depositCircuit,
    r1csPath: depositR1cs,
    zkeyPrefix: path.join(BUILD_DIR, "deposit"),
    vkPath: path.join(BUILD_DIR, "deposit_verification_key.json"),
    generatedSolTmp: path.join(BUILD_DIR, "deposit_verifier_tmp.sol"),
    generatedSolOut: path.join(CONTRACTS_ZK_DIR, "GeneratedDepositVerifier.sol"),
    contractName: "BermudaDepositGroth16Verifier",
    ptauPath: ptau,
  });

  process.stdout.write(`ok: verifiers written to ${CONTRACTS_ZK_DIR}\n`);
}

main();
