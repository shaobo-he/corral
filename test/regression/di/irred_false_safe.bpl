// Regression for duplicate si_unique_call IDs introduced while Boogie makes an
// irreducible CFG reducible. Run this once as ordinary SI and once with /di.
// Before the DI fail-closed fix, ordinary SI finds the bug but /di incorrectly
// reports SAFE after merging the sequential calls to check.
procedure check(a: int)
{
  assert a == 0;
}

procedure {:entrypoint} main()
{
  var x: int;
  x := 0;
  goto A, B;

  A:
    call check(x);
    goto B;

  B:
    call check(x);
    call check(x);
    x := 1;
    call check(x);
    goto A, C;

  C:
    assert true;
}
