// Same irreducible CFG without the calls: the mis-mapped blocks used to surface
// later, as "Refinement unable to make progress".
procedure main()
{
  var x: int;
  x := 0;
  goto A, B;
  A:
    x := x + 1;
    goto B;
  B:
    x := x + 1;
    goto A, C;
  C:
    assert x < 3;
}
