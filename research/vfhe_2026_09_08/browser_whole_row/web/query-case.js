// Application-selected pins for the all-row reproof of the saved fast001 public cases.
const freeze = value => { if (value && typeof value === "object") { for (const item of Object.values(value)) freeze(item); Object.freeze(value); } return value; };
export const QUERY_CASE = freeze({
  "schema": "recorded-two-class-query-wasm-v1",
  "id": "fast001-all-row-reproof-two-class-query",
  "requestId": "new-two-class-query",
  "expectedBackend": "plonky3-hidingfri-babybear-ir2@82cfad73cd734d37a0d51953094f970c531817ec|lb3|lfp0|arity3|q38|qpow16|ext4|salt4|random-codewords4|public-preprocessing-xoshiro256pp-0.8.1-v1",
  "expectedTemplateSha256": "504ec55e5421ec3116fff563974a1ef6f849fb08caea20daec3f0fcf72c9c933",
  "templatePath": "fixtures/template.json",
  "requestPath": "fixtures/request.json",
  "wasmPath": "web/pkg/vfhe_browser_verifier_bg.wasm",
  "publicQuerySha256": "b3d468fd195b2f696ac5c93be3f3c374142e532f04f6af860f6a96fdc035eb39",
  "recordedModelRoot": "742982ae2402dc944074f0df249d412040ef273df392803810a92c434c807204",
  "recordedRevision": 2,
  "scope": "Both recorded fast001 class ciphertext query computations, newly proved with arithmetic gates on all 8192 physical rows. No encoder, decryption, authorization, or universal native verifier soundness proof.",
  "cases": [
    {
      "label": "card_arrival",
      "publicRowsPath": "fixtures/class0/public_rows.json",
      "proofPath": "fixtures/class0/proof.bin",
      "rows": 8192,
      "publicWidth": 57,
      "accumulatorSha256": "e36c2748096178b7630a165f5e22ed6e6292a7fa08b1bc3dc81d7d3caf12286b",
      "outputCiphertextSha256": "14e77e552b91d4df4c776c1a630a0c488fda4e3b0755a779ca4a9c1ea3cc28f3"
    },
    {
      "label": "cash_withdrawal_charge",
      "publicRowsPath": "fixtures/class1/public_rows.json",
      "proofPath": "fixtures/class1/proof.bin",
      "rows": 8192,
      "publicWidth": 57,
      "accumulatorSha256": "883539e89f9eeba07e52194901c5568652b8c756b092d106d19672a1f95cb9f6",
      "outputCiphertextSha256": "a8929c88da8861ec1cf81b7f34411b302a09bd434c237b6b01bac71ca442ccc6"
    }
  ],
  "files": {
    "web/package.json": {
      "bytes": 34,
      "sha256": "55c40fada2c832d834f915351168d4a46598bde8070f076b72ab6b45d53b3da5"
    },
    "web/verifier.js": {
      "bytes": 1122,
      "sha256": "3f8f73180eac337b0b2210d3490f225dc7691b86b0a2d40db7284847ae524f24"
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
    "fixtures/template.json": {
      "bytes": 633446,
      "sha256": "504ec55e5421ec3116fff563974a1ef6f849fb08caea20daec3f0fcf72c9c933"
    },
    "fixtures/class0/public_rows.json": {
      "bytes": 1355833,
      "sha256": "abe798ede5a79d84c5ad28449210968912c794b1ab042fe821280965fc9a30c3"
    },
    "fixtures/class0/proof.bin": {
      "bytes": 842472,
      "sha256": "139f93baa04cad3b843d4f6823d7f0c94d370de0944448ea8b23b5d50770f5e7"
    },
    "fixtures/class1/public_rows.json": {
      "bytes": 1356003,
      "sha256": "190efb0aa303172501e247b60d312f59ff51d783e28050778b9eb634239d0180"
    },
    "fixtures/class1/proof.bin": {
      "bytes": 842594,
      "sha256": "c846d1bbef6fed6a905ce0d1c558f79ba8494c649c9f9e6a5686a4f934be4802"
    },
    "fixtures/request.json": {
      "bytes": 3237,
      "sha256": "d59d7ee99d4eac8a2cf5b51a2570546769f46595942f44c35eb6d4d6ce5991f8"
    }
  }
});
