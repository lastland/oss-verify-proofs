From OssFuzzTheorems.cjson.cjson_read_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Glue Require TopGlue.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.

Theorem ubsan_agrees_holds : OssFuzzTheorems.cjson.cjson_read_fuzzer.Statements.ubsan_agrees.
Proof.
  apply LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_of_scfg.
  exact OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Glue.TopGlue.ubsan_base.
Qed.
