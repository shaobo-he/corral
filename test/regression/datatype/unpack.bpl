// Boogie 3.5.6 added UnpackCmd ("C(x, y) := e"). corral desugars it as the
// program is read; without that, variable slicing rejects the command outright.
datatype List { Nil(), Cons(head: int, tail: List) }

procedure {:entrypoint} main()
{
  var h: int;
  var t: List;
  var l: List;
  l := Cons(1, Nil());
  Cons(h, t) := l;
  assert h == 99;
}
