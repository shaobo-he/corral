// Genuinely exhausts the recursion bound, so corral must report a bounded pass.
// Boogie 3.5.6 deleted Outcome.ReachedBound, so bound exhaustion travels as
// Inconclusive -- the same value a solver "unknown" produces. This pins down that
// the real bound exhaustion is still reported as "Program has no bugs" and not
// turned into an error along with the solver failures.
procedure rec(n: int) returns (r: int)
{
  if (n <= 0) { r := 0; return; }
  call r := rec(n - 1);
  r := r + 1;
}

procedure main()
{
  var x: int;
  call x := rec(100);
  assert x >= 0;
}
