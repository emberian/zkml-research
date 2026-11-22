# Wave 8 Next Steps & Maintainer Handoff

1. **Fold into `docs/VERDICTS.md`:** Maintainer may fold the closed `G1–G8`, `G11`, `G12`, `D2`, `D5`, `D7`, `D8`, and `S1–S7`/`S11` gates from `notes/wave8*.md` and `notes/wave8b*.md` into `docs/VERDICTS.md` (`[OPEN]`).
2. **Downstream On-Chain Targets (`G12`):** Generate concrete target-chain verifier contracts (EVM Yul/Solidity, CosmWasm, Solana BPF Token-2022) against the mechanized `Obend.Apps.SovereignDrex` `auditL1SettlementBatch` and `L1VaultInstructionKind` schemas (`[OPEN]`).
3. **Full `Pancake -> WordLang -> CakeML` Backend Tail (`G6`):** Extend `Obend.Lower.Pancake` down through register allocation and machine-code emission (`[OPEN]`).
