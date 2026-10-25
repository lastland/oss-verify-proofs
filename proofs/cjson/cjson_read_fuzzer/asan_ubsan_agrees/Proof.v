From OssFuzzTheorems.cjson.cjson_read_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.B Require TopBothClosed.

Theorem asan_ubsan_agrees_holds : OssFuzzTheorems.cjson.cjson_read_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.B.TopBothClosed.both_base_san. Qed.
