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

async function generateDepositProof({ noteSecret, noteSalt, amount }) {
  const poseidon = await buildPoseidon();
  const F = poseidon.F;

  const h1 = poseidon([noteSecret, noteSalt]);
  const commitment = poseidon([h1, amount]);

  const buildDir = appPath("circuits", "build");
  const wasmPath = path.join(buildDir, "bermudaNoteDeposit_js", "bermudaNoteDeposit.wasm");
  const zkeyPath = path.join(buildDir, "deposit_final.zkey");
  if (!fs.existsSync(wasmPath)) throw new Error(`Missing wasm at ${wasmPath}`);
  if (!fs.existsSync(zkeyPath)) throw new Error(`Missing zkey at ${zkeyPath}`);

  const input = {
    noteSecret: noteSecret.toString(),
    noteSalt: noteSalt.toString(),
    amount: amount.toString(),
    commitment: F.toObject(commitment).toString(),
  };

  const { proof, publicSignals } = await snarkjs.groth16.fullProve(input, wasmPath, zkeyPath);

  // snarkjs -> Solidity calldata (same transformation used in apps/base-contracts/scripts/generate-proof.js)
  const solidityProof = {
    a: [proof.pi_a[0], proof.pi_a[1]],
    b: [
      [proof.pi_b[0][1], proof.pi_b[0][0]],
      [proof.pi_b[1][1], proof.pi_b[1][0]],
    ],
    c: [proof.pi_c[0], proof.pi_c[1]],
  };

  return {
    solidityProof,
    publicSignals,
    commitment: BigInt(input.commitment),
  };
}

describe("Bermuda POC: deposit proof binding", function () {
  this.timeout(10 * 60 * 1000);

  before(function () {
    const zkey = appPath("circuits", "build", "deposit_final.zkey");
    const wasm = appPath("circuits", "build", "bermudaNoteDeposit_js", "bermudaNoteDeposit.wasm");
    if (fs.existsSync(zkey) && fs.existsSync(wasm)) return;
    sh("npm run build:verifiers", appPath());
  });

  it("accepts a deposit with a valid deposit proof", async function () {
    const [deployer] = await ethers.getSigners();

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

    const amount = 5000n;
    await (await token.mint(deployer.address, amount)).wait();
    await (await token.approve(await pool.getAddress(), amount)).wait();

    const { solidityProof, publicSignals, commitment } = await generateDepositProof({
      noteSecret: 123n,
      noteSalt: 456n,
      amount,
    });

    assert.strictEqual(BigInt(publicSignals[0]), amount);
    assert.strictEqual(BigInt(publicSignals[1]), commitment);

    await (await pool.deposit(solidityProof, { amount, commitment })).wait();

    const poolBal = await token.balanceOf(await pool.getAddress());
    assert.strictEqual(poolBal, amount);
  });

  it("rejects a deposit when the commitment is malformed (proof/public mismatch)", async function () {
    const [deployer] = await ethers.getSigners();

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

    const amount = 5000n;
    await (await token.mint(deployer.address, amount)).wait();
    await (await token.approve(await pool.getAddress(), amount)).wait();

    const { solidityProof, commitment } = await generateDepositProof({
      noteSecret: 999n,
      noteSalt: 111n,
      amount,
    });

    const badCommitment = commitment + 1n;

    let threw = false;
    try {
      await (await pool.deposit(solidityProof, { amount, commitment: badCommitment })).wait();
    } catch (err) {
      threw = true;
      const msg = err?.message ?? String(err);
      assert.match(msg, /InvalidProof/i);
    }
    assert.strictEqual(threw, true);
  });
});

