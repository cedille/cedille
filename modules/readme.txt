type-qualif.diff
----------------
Assumes input type to check is qualified.
Bug appears in examples/proof-reuse/ListReuse.ced

qualif-type.diff
----------------
Assumes input type to check is unqualifed.
Bug appears in proof-reuse/Cast.ced

Originally I thought assuming the input type to check
is qualified would be fine, as in type-qualif.diff. But
a lot of checking the code is written using a mutual function
that assumes an un-normalized input type (check-term), which
normalizes for its mutually defined counterpart (check-termi). So
in qualif-type.diff I changed to similarly not assume that the input type
of check-term is qualified, but assume qualified in check-termi.
Unfortunately, both versions currently contain different bugs that I have
not been able to fix so far.
