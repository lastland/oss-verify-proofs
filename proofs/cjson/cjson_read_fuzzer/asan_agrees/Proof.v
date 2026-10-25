From OssFuzzTheorems.cjson.cjson_read_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.A Require TopAsanClosed.

Theorem asan_agrees_holds : OssFuzzTheorems.cjson.cjson_read_fuzzer.Statements.asan_agrees.
Proof. exact OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.A.TopAsanClosed.asan_base_san. Qed.
