// Mirror of unpack.bpl with the assertion that should hold.
datatype List { Nil(), Cons(head: int, tail: List) }

procedure {:entrypoint} main()
{
  var h: int;
  var t: List;
  var l: List;
  l := Cons(1, Nil());
  Cons(h, t) := l;
  assert h == 1;
}
