// Two maps that agree at every index are equal, but proving `b == c` from
// pointwise facts needs Z3's array extensionality. The input compares maps, so
// corral turns extensionality on by itself and the assertion holds.
procedure main()
{
  var a, b, c: [int]int;
  var i, j, x, y: int;

  assume i != j;
  b := a[i := x][j := y];
  c := a[j := y][i := x];
  assert b == c;
}
