// Application-selected transport pins for this exact retained public case.
const freeze = value => { if (value && typeof value === "object") { for (const item of Object.values(value)) freeze(item); Object.freeze(value); } return value; };
export const QUERY_CASE = freeze({
  "schema": "recorded-two-class-query-wasm-v1",
  "id": "gated001-new-two-class-query",
  "requestId": "new-two-class-query",
  "expectedBackend": "plonky3-hidingfri-babybear-ir2@82cfad73cd734d37a0d51953094f970c531817ec|lb3|lfp0|arity3|q38|qpow16|ext4|salt4|random-codewords4|public-preprocessing-xoshiro256pp-0.8.1-v1",
  "expectedTemplateSha256": "f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d",
  "templatePath": "fixtures/template.json",
  "requestPath": "fixtures/request.json",
  "wasmPath": "web/pkg/vfhe_browser_verifier_bg.wasm",
  "publicQuerySha256": "b3d468fd195b2f696ac5c93be3f3c374142e532f04f6af860f6a96fdc035eb39",
  "recordedModelRoot": "74c1361182b0ef7c12ce3066d87517b0388038704fca9021550f0117255f7d04",
  "recordedRevision": 2,
  "scope": "Both recorded class ciphertext query computations: two signed products and subtraction. No encoder, decryption or authorization proof.",
  "cases": [
    {
      "label": "card_arrival",
      "publicRowsPath": "fixtures/class0/public_rows.json",
      "proofPath": "fixtures/class0/proof.bin",
      "rows": 8192,
      "publicWidth": 57,
      "accumulatorSha256": "74ec6d548b5bcb0394d5e5982110b33fe15f223953d9805bd68be6a7d65bc509",
      "outputCiphertextSha256": "db996106e532f279f0a3f59ad4a7561b6e859e5e568c98dd4600fb83ccfa74d5"
    },
    {
      "label": "cash_withdrawal_charge",
      "publicRowsPath": "fixtures/class1/public_rows.json",
      "proofPath": "fixtures/class1/proof.bin",
      "rows": 8192,
      "publicWidth": 57,
      "accumulatorSha256": "3cbf4f3a75a6dda15dc7d1da1eab521d9497fde8a0a20aaeebc697ecd666322c",
      "outputCiphertextSha256": "7b878ed70d4b9f9eb0ea1d07fc0e3b1a1f5be02322584dbd3c415a9e06dff018"
    }
  ],
  "files": {
    "web/package.json": {
      "bytes": 34,
      "sha256": "55c40fada2c832d834f915351168d4a46598bde8070f076b72ab6b45d53b3da5"
    },
    "web/pkg/vfhe_browser_verifier.d.ts": {
      "bytes": 1942,
      "sha256": "481b151baa99a73ff118ad192d56e67732d15e09ba26de4088be7635a469b054"
    },
    "web/pkg/vfhe_browser_verifier.js": {
      "bytes": 8325,
      "sha256": "58e31dbd078d6769aea5f7518900d55d93422c6eddf065425b0a00c133102f0e"
    },
    "web/pkg/vfhe_browser_verifier_bg.wasm": {
      "bytes": 2063586,
      "sha256": "96137c1ed0ad5fc7584ca72ef006ff70ac1951831408ee12ab22ce3879f6f908"
    },
    "web/pkg/vfhe_browser_verifier_bg.wasm.d.ts": {
      "bytes": 725,
      "sha256": "9d6af5e8addb975cd6f3534cc6144ccff96c48cbd2aa4e2e399c85c7da67aeac"
    },
    "web/verifier.js": {
      "bytes": 1122,
      "sha256": "3f8f73180eac337b0b2210d3490f225dc7691b86b0a2d40db7284847ae524f24"
    },
    "fixtures/template.json": {
      "bytes": 553870,
      "sha256": "f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d"
    },
    "fixtures/request.json": {
      "bytes": 2174,
      "sha256": "69167d12c0f9fe53847f3172e9c55f91c62bf3809dc8190d68a68511014ec765"
    },
    "fixtures/class0/public_rows.json": {
      "bytes": 1355905,
      "sha256": "3c335d3184f0a5051066bbfab17c6135782f72b12a7ce654fcf35037b682e505"
    },
    "fixtures/class0/proof.bin": {
      "bytes": 842647,
      "sha256": "bbd292c8cc76f5d2cadb832f9f380cabd41185b202683940281098f0560cc8a7"
    },
    "fixtures/class1/public_rows.json": {
      "bytes": 1355855,
      "sha256": "3d0b5ef3d2b007cb4b9c186e5fdb643cd1645f6f7d4fba65a762dbcf723da2d2"
    },
    "fixtures/class1/proof.bin": {
      "bytes": 842459,
      "sha256": "1c49d589330a34544228c1c6b50750187cf71d54b5a57cfefbcbf41cb261f8ef"
    }
  }
});
