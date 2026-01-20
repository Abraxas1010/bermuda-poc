const assert = require("assert");
const fs = require("fs");
const path = require("path");
const { execSync } = require("child_process");

const snarkjs = require("snarkjs");
const { buildPoseidon, poseidonContract } = require("circomlibjs");

const { ethers } = require("hardhat");

function sh(cmd, cwd) {
  execSync(cmd, {
    cwd,
    stdio: "inherit",
    env: { ...process.env, DEBUG: "" },
  });
}

function appPath(...parts) {
  return path.join(__dirname, "..", ...parts);
}

async function deployPoseidonT2(signer) {
  const initcode = poseidonContract.createCode(2);
  const tx = await signer.sendTransaction({ data: initcode, gasLimit: 6_000_000n });
  const receipt = await tx.wait();
  if (!receipt || !receipt.contractAddress) throw new Error("Poseidon deploy failed");
  return receipt.contractAddress;
}

async function getZeros(registry) {
  const zs = [];
  for (let i = 0; i < 20; i++) {
    // Public fixed-size array getter.
    // eslint-disable-next-line no-await-in-loop
    const z = await registry.zeros(i);
    zs.push(BigInt(z));
  }
  return zs;
}

async function computeMerklePath({ registry, leaves, zeros, leafIndex }) {
  if (leafIndex < 0 || leafIndex >= leaves.length) throw new Error("leafIndex out of range");

  let idx = leafIndex;
  let level = leaves.map((x) => BigInt(x));
  const pathElements = [];
  const pathIndices = [];

  for (let depth = 0; depth < 20; depth++) {
    if (level.length % 2 === 1) level = level.concat([zeros[depth]]);

    const isRight = idx % 2 === 1;
    const siblingIdx = isRight ? idx - 1 : idx + 1;
    const sibling = siblingIdx < level.length ? level[siblingIdx] : zeros[depth];
    pathElements.push(sibling);
    pathIndices.push(isRight ? 1 : 0);

    const parents = [];
    for (let i = 0; i < level.length; i += 2) {
      // eslint-disable-next-line no-await-in-loop
      const h = await registry.hashLeftRight(level[i], level[i + 1]);
      parents.push(BigInt(h));
    }
    level = parents;
    idx = Math.floor(idx / 2);
  }

  return {
    root: level[0],
    pathElements,
    pathIndices,
  };
}

function toUint160(addr) {
  return BigInt(addr) & ((1n << 160n) - 1n);
}

async function silenceStdio(fn) {
  const outWrite = process.stdout.write;
  const errWrite = process.stderr.write;
  process.stdout.write = () => true;
  process.stderr.write = () => true;
  try {
    return await fn();
  } finally {
    process.stdout.write = outWrite;
    process.stderr.write = errWrite;
  }
}

async function generateDepositProof({ noteSecret, noteSalt, amount }) {
  const poseidon = await buildPoseidon();
  const F = poseidon.F;

  const h1 = poseidon([noteSecret, noteSalt]);
  const commitment = poseidon([h1, amount]);

  const buildDir = appPath("circuits", "build");
  const wasmPath = path.join(buildDir, "bermudaNoteDeposit_js", "bermudaNoteDeposit.wasm");
  const zkeyPath = path.join(buildDir, "deposit_final.zkey");

  const input = {
    noteSecret: noteSecret.toString(),
    noteSalt: noteSalt.toString(),
    amount: amount.toString(),
    commitment: F.toObject(commitment).toString(),
  };

  const { proof } = await snarkjs.groth16.fullProve(input, wasmPath, zkeyPath);

  const solidityProof = {
    a: [proof.pi_a[0], proof.pi_a[1]],
    b: [
      [proof.pi_b[0][1], proof.pi_b[0][0]],
      [proof.pi_b[1][1], proof.pi_b[1][0]],
    ],
    c: [proof.pi_c[0], proof.pi_c[1]],
  };

  return { solidityProof, commitment: BigInt(input.commitment) };
}

async function generateWithdrawProof({
  licenseRoot,
  kycRoot,
  noteRoot,
  nullifier,
  recipient,
  amount,
  operatorAddress,
  operatorCredentialId,
  operatorLicenseClass,
  operatorSecret,
  operatorPathElements,
  operatorPathIndices,
  senderAddress,
  senderCredentialId,
  senderKycLevel,
  senderSecret,
  senderPathElements,
  senderPathIndices,
  zeros,
  noteSecret,
  noteSalt,
  notePathElements,
  notePathIndices,
}) {
  const buildDir = appPath("circuits", "build");
  const wasmPath = path.join(buildDir, "bermudaWithdrawCompliance_js", "bermudaWithdrawCompliance.wasm");
  const zkeyPath = path.join(buildDir, "withdraw_final.zkey");

  const input = {
    operatorAddress: operatorAddress.toString(),
    operatorCredentialId: operatorCredentialId.toString(),
    operatorLicenseClass: operatorLicenseClass.toString(),
    operatorSecret: operatorSecret.toString(),
    operatorPathElements: operatorPathElements.map(String),
    operatorPathIndices: operatorPathIndices.map(String),

    senderAddress: senderAddress.toString(),
    senderCredentialId: senderCredentialId.toString(),
    senderKycLevel: senderKycLevel.toString(),
    senderSecret: senderSecret.toString(),
    senderPathElements: senderPathElements.map(String),
    senderPathIndices: senderPathIndices.map(String),

    noteSecret: noteSecret.toString(),
    noteSalt: noteSalt.toString(),
    notePathElements: notePathElements.map(String),
    notePathIndices: notePathIndices.map(String),

    licenseRoot: licenseRoot.toString(),
    kycRoot: kycRoot.toString(),
    noteRoot: noteRoot.toString(),
    nullifier: nullifier.toString(),
    recipient: recipient.toString(),
    amount: amount.toString(),
  };

  const { proof, publicSignals } = await snarkjs.groth16.fullProve(input, wasmPath, zkeyPath);

  const solidityProof = {
    a: [proof.pi_a[0], proof.pi_a[1]],
    b: [
      [proof.pi_b[0][1], proof.pi_b[0][0]],
      [proof.pi_b[1][1], proof.pi_b[1][0]],
    ],
    c: [proof.pi_c[0], proof.pi_c[1]],
  };

  return { solidityProof, publicSignals };
}

describe("Bermuda POC: withdraw proof end-to-end", function () {
  this.timeout(15 * 60 * 1000);

  before(function () {
    const wasm = appPath("circuits", "build", "bermudaWithdrawCompliance_js", "bermudaWithdrawCompliance.wasm");
    const zkey = appPath("circuits", "build", "withdraw_final.zkey");
    const depWasm = appPath("circuits", "build", "bermudaNoteDeposit_js", "bermudaNoteDeposit.wasm");
    const depZkey = appPath("circuits", "build", "deposit_final.zkey");
    if (fs.existsSync(wasm) && fs.existsSync(zkey) && fs.existsSync(depWasm) && fs.existsSync(depZkey)) return;
    sh("npm run build:verifiers", appPath());
  });

  it("withdraws with a valid compliance proof and prevents double spend", async function () {
    const [deployer, operator, sender, recipient] = await ethers.getSigners();

    const poseidonT2 = await deployPoseidonT2(deployer);

    const License = await ethers.getContractFactory("BermudaLicenseRegistry");
    const KYC = await ethers.getContractFactory("BermudaKYCRegistry");
    const Notes = await ethers.getContractFactory("BermudaNoteRegistry");
    const license = await License.deploy(poseidonT2);
    await license.waitForDeployment();
    const kyc = await KYC.deploy(poseidonT2);
    await kyc.waitForDeployment();
    const notes = await Notes.deploy(poseidonT2);
    await notes.waitForDeployment();

    const DepositVerifier = await ethers.getContractFactory("BermudaDepositVerifier");
    const WithdrawVerifier = await ethers.getContractFactory("BermudaWithdrawVerifier");
    const depositVerifier = await DepositVerifier.deploy();
    await depositVerifier.waitForDeployment();
    const withdrawVerifier = await WithdrawVerifier.deploy();
    await withdrawVerifier.waitForDeployment();

    const Token = await ethers.getContractFactory("MockERC20");
    const token = await Token.deploy("MockUSDC", "mUSDC", 6);
    await token.waitForDeployment();

    const Pool = await ethers.getContractFactory("BermudaCompliantShieldedPool");
    const pool = await Pool.deploy(
      await token.getAddress(),
      await license.getAddress(),
      await kyc.getAddress(),
      await notes.getAddress(),
      await withdrawVerifier.getAddress(),
      await depositVerifier.getAddress(),
    );
    await pool.waitForDeployment();

    await (await notes.authorizeInserter(await pool.getAddress(), true)).wait();

    const zeros = await getZeros(license);
    const poseidon = await buildPoseidon();
    const F = poseidon.F;

    // Fill registries with multiple leaves so we exercise non-trivial Merkle paths.
    // We'll target leafIndex=3 for license + KYC + note commitments.
    const licenseLeaves = [];
    const kycLeaves = [];
    const noteLeaves = [];

    // License leaves
    for (let i = 0; i < 3; i++) {
      // eslint-disable-next-line no-await-in-loop
      const leaf = await license.computeLicenseLeaf(deployer.address, 10 + i, 0, 100 + i);
      licenseLeaves.push(BigInt(leaf));
      // eslint-disable-next-line no-await-in-loop
      await (await license.addLicense(deployer.address, 10 + i, 0, 100 + i)).wait();
    }
    {
      const leaf = await license.computeLicenseLeaf(operator.address, 1, 0, 777);
      licenseLeaves.push(BigInt(leaf));
      await (await license.addLicense(operator.address, 1, 0, 777)).wait();
    }

    // KYC leaves
    for (let i = 0; i < 3; i++) {
      // eslint-disable-next-line no-await-in-loop
      const leaf = await kyc.computeKycLeaf(deployer.address, 10 + i, 1, 200 + i);
      kycLeaves.push(BigInt(leaf));
      // eslint-disable-next-line no-await-in-loop
      await (await kyc.addKycCredential(deployer.address, 10 + i, 1, 200 + i)).wait();
    }
    {
      const leaf = await kyc.computeKycLeaf(sender.address, 1, 1, 888);
      kycLeaves.push(BigInt(leaf));
      await (await kyc.addKycCredential(sender.address, 1, 1, 888)).wait();
    }

    // Note deposits (proof-bound). We'll deposit 4 notes and withdraw the 4th.
    const depositAmounts = [100000n, 200000n, 300000n, 400000n];
    const noteSecrets = [11n, 22n, 33n, 44n];
    const noteSalts = [111n, 222n, 333n, 444n];

    const totalDeposit = depositAmounts.reduce((a, b) => a + b, 0n);
    await (await token.mint(deployer.address, totalDeposit)).wait();
    await (await token.approve(await pool.getAddress(), totalDeposit)).wait();

    for (let i = 0; i < 4; i++) {
      // eslint-disable-next-line no-await-in-loop
      const dep = await generateDepositProof({
        noteSecret: noteSecrets[i],
        noteSalt: noteSalts[i],
        amount: depositAmounts[i],
      });
      noteLeaves.push(dep.commitment);
      // eslint-disable-next-line no-await-in-loop
      await (await pool.deposit(dep.solidityProof, { amount: depositAmounts[i], commitment: dep.commitment })).wait();
    }

    const licenseRoot = await license.getMerkleRoot();
    const kycRoot = await kyc.getMerkleRoot();
    const noteRoot = await notes.getMerkleRoot();

    const licensePath = await computeMerklePath({ registry: license, leaves: licenseLeaves, zeros, leafIndex: 3 });
    const kycPath = await computeMerklePath({ registry: kyc, leaves: kycLeaves, zeros, leafIndex: 3 });
    const notePath = await computeMerklePath({ registry: notes, leaves: noteLeaves, zeros, leafIndex: 3 });

    assert.strictEqual(licensePath.root.toString(), BigInt(licenseRoot).toString());
    assert.strictEqual(kycPath.root.toString(), BigInt(kycRoot).toString());
    assert.strictEqual(notePath.root.toString(), BigInt(noteRoot).toString());

    const withdrawAmount = depositAmounts[3];
    const noteSecret = noteSecrets[3];
    const noteSalt = noteSalts[3];

    // Nullifier must match circuit’s NoteNullifier.
    const nullifier = BigInt(F.toObject(poseidon([noteSecret, noteSalt])));

    const recipient160 = toUint160(recipient.address);
    const operator160 = toUint160(operator.address);
    const sender160 = toUint160(sender.address);

    const w = await generateWithdrawProof({
      licenseRoot: BigInt(licenseRoot),
      kycRoot: BigInt(kycRoot),
      noteRoot: BigInt(noteRoot),
      nullifier,
      recipient: recipient160,
      amount: withdrawAmount,
      operatorAddress: operator160,
      operatorCredentialId: 1n,
      operatorLicenseClass: 0n,
      operatorSecret: 777n,
      operatorPathElements: licensePath.pathElements,
      operatorPathIndices: licensePath.pathIndices,
      senderAddress: sender160,
      senderCredentialId: 1n,
      senderKycLevel: 1n,
      senderSecret: 888n,
      senderPathElements: kycPath.pathElements,
      senderPathIndices: kycPath.pathIndices,
      zeros,
      noteSecret,
      noteSalt,
      notePathElements: notePath.pathElements,
      notePathIndices: notePath.pathIndices,
    });

    // Sanity: public signals match what we intend to submit.
    assert.strictEqual(BigInt(w.publicSignals[0]), BigInt(licenseRoot));
    assert.strictEqual(BigInt(w.publicSignals[1]), BigInt(kycRoot));
    assert.strictEqual(BigInt(w.publicSignals[2]), BigInt(noteRoot));
    assert.strictEqual(BigInt(w.publicSignals[3]), nullifier);
    assert.strictEqual(BigInt(w.publicSignals[4]), recipient160);
    assert.strictEqual(BigInt(w.publicSignals[5]), withdrawAmount);

    await (
      await pool.withdraw(w.solidityProof, {
        licenseRoot,
        kycRoot,
        noteRoot,
        nullifier,
        recipient: recipient160,
        amount: withdrawAmount,
      })
    ).wait();

    const recipientBal = await token.balanceOf(recipient.address);
    assert.strictEqual(recipientBal, withdrawAmount);
    const poolBal = await token.balanceOf(await pool.getAddress());
    assert.strictEqual(poolBal, totalDeposit - withdrawAmount);

    // Double-spend attempt should revert.
    let threw = false;
    try {
      await (
        await pool.withdraw(w.solidityProof, {
          licenseRoot,
          kycRoot,
          noteRoot,
          nullifier,
          recipient: recipient160,
          amount: withdrawAmount,
        })
      ).wait();
    } catch (err) {
      threw = true;
      const msg = err?.message ?? String(err);
      assert.match(msg, /NullifierAlreadyUsed/i);
    }
    assert.strictEqual(threw, true);
  });

  it("cannot generate a proof for a non-compliant KYC level", async function () {
    const [deployer, operator, sender, recipient] = await ethers.getSigners();
    const poseidonT2 = await deployPoseidonT2(deployer);

    const License = await ethers.getContractFactory("BermudaLicenseRegistry");
    const KYC = await ethers.getContractFactory("BermudaKYCRegistry");
    const Notes = await ethers.getContractFactory("BermudaNoteRegistry");
    const license = await License.deploy(poseidonT2);
    await license.waitForDeployment();
    const kyc = await KYC.deploy(poseidonT2);
    await kyc.waitForDeployment();
    const notes = await Notes.deploy(poseidonT2);
    await notes.waitForDeployment();

    const DepositVerifier = await ethers.getContractFactory("BermudaDepositVerifier");
    const WithdrawVerifier = await ethers.getContractFactory("BermudaWithdrawVerifier");
    const depositVerifier = await DepositVerifier.deploy();
    await depositVerifier.waitForDeployment();
    const withdrawVerifier = await WithdrawVerifier.deploy();
    await withdrawVerifier.waitForDeployment();

    const Token = await ethers.getContractFactory("MockERC20");
    const token = await Token.deploy("MockUSDC", "mUSDC", 6);
    await token.waitForDeployment();

    const Pool = await ethers.getContractFactory("BermudaCompliantShieldedPool");
    const pool = await Pool.deploy(
      await token.getAddress(),
      await license.getAddress(),
      await kyc.getAddress(),
      await notes.getAddress(),
      await withdrawVerifier.getAddress(),
      await depositVerifier.getAddress(),
    );
    await pool.waitForDeployment();

    await (await notes.authorizeInserter(await pool.getAddress(), true)).wait();

    const zeros = await getZeros(license);
    const poseidon = await buildPoseidon();
    const F = poseidon.F;

    const licenseLeaves = [];
    const kycLeaves = [];
    const noteLeaves = [];

    // Ensure non-zero index here too (target leafIndex=1).
    {
      const leaf = await license.computeLicenseLeaf(deployer.address, 10, 0, 100);
      licenseLeaves.push(BigInt(leaf));
      await (await license.addLicense(deployer.address, 10, 0, 100)).wait();
    }
    {
      const leaf = await license.computeLicenseLeaf(operator.address, 1, 0, 777);
      licenseLeaves.push(BigInt(leaf));
      await (await license.addLicense(operator.address, 1, 0, 777)).wait();
    }
    {
      const leaf = await kyc.computeKycLeaf(deployer.address, 10, 1, 200);
      kycLeaves.push(BigInt(leaf));
      await (await kyc.addKycCredential(deployer.address, 10, 1, 200)).wait();
    }
    {
      // Sender is BASIC here (level=0)
      const leaf = await kyc.computeKycLeaf(sender.address, 1, 0, 888);
      kycLeaves.push(BigInt(leaf));
      await (await kyc.addKycCredential(sender.address, 1, 0, 888)).wait();
    }

    const amount = 500000n; // exceeds basic limit (100000)
    const noteSecret = 123n;
    const noteSalt = 456n;

    await (await token.mint(deployer.address, amount)).wait();
    await (await token.approve(await pool.getAddress(), amount)).wait();
    const dep = await generateDepositProof({ noteSecret, noteSalt, amount });
    noteLeaves.push(dep.commitment);
    await (await pool.deposit(dep.solidityProof, { amount, commitment: dep.commitment })).wait();

    const nullifier = BigInt(F.toObject(poseidon([noteSecret, noteSalt])));
    const recipient160 = toUint160(recipient.address);

    const licenseRoot = await license.getMerkleRoot();
    const kycRoot = await kyc.getMerkleRoot();
    const noteRoot = await notes.getMerkleRoot();

    const licensePath = await computeMerklePath({ registry: license, leaves: licenseLeaves, zeros, leafIndex: 1 });
    const kycPath = await computeMerklePath({ registry: kyc, leaves: kycLeaves, zeros, leafIndex: 1 });
    const notePath = await computeMerklePath({ registry: notes, leaves: noteLeaves, zeros, leafIndex: 0 });

    assert.strictEqual(licensePath.root.toString(), BigInt(licenseRoot).toString());
    assert.strictEqual(kycPath.root.toString(), BigInt(kycRoot).toString());
    assert.strictEqual(notePath.root.toString(), BigInt(noteRoot).toString());

    let threw = false;
    try {
      await silenceStdio(async () => {
        await generateWithdrawProof({
          licenseRoot: BigInt(licenseRoot),
          kycRoot: BigInt(kycRoot),
          noteRoot: BigInt(noteRoot),
          nullifier,
          recipient: recipient160,
          amount,
          operatorAddress: toUint160(operator.address),
          operatorCredentialId: 1n,
          operatorLicenseClass: 0n,
          operatorSecret: 777n,
          operatorPathElements: licensePath.pathElements,
          operatorPathIndices: licensePath.pathIndices,
          senderAddress: toUint160(sender.address),
          senderCredentialId: 1n,
          senderKycLevel: 0n,
          senderSecret: 888n,
          senderPathElements: kycPath.pathElements,
          senderPathIndices: kycPath.pathIndices,
          zeros,
          noteSecret,
          noteSalt,
          notePathElements: notePath.pathElements,
          notePathIndices: notePath.pathIndices,
        });
      });
    } catch {
      threw = true;
    }

    assert.strictEqual(threw, true);
  });
});
