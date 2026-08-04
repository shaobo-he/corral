// Irreducible loop (A and B are mutually reachable and both are entries).
// Boogie 3.5.6 makes the CFG reducible by splitting nodes into "<label>_dup_<n>"
// blocks, which do not exist in the pre-extraction snapshot corral reconstructs
// traces against. When such a block carries a call, the walk used to abort with
// "An intermediate block has a procedure call" instead of reporting the bug.
procedure inc(a: int) returns (b: int)
{
  b := a + 1;
}

procedure main()
{
  var x: int;
  x := 0;
  goto A, B;
  A:
    call x := inc(x);
    goto B;
  B:
    call x := inc(x);
    goto A, C;
  C:
    assert x < 3;
}
