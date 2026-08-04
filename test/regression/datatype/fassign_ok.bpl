// Mirror of fassign.bpl: the same field assignment, asserted the other way
// round. Together they pin the verdict down from both sides -- dropping the
// assignment flips exactly one of the two.
datatype List { Nil(), Cons(head: int, tail: List) }

procedure {:entrypoint} main()
{
  var l: List;
  l := Cons(1, Nil());
  l->head := 5;
  assert l->head == 5;
}
