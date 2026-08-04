// Boogie 3.5.6 added FieldAssignLhs. corral's duplicator has to clone it, or
// the copy shares the node with the original and the assignment is silently
// lost -- "l->head := 5" below would leave l->head == 1 and corral would
// wrongly report no bugs.
datatype List { Nil(), Cons(head: int, tail: List) }

procedure {:entrypoint} main()
{
  var l: List;
  l := Cons(1, Nil());
  l->head := 5;
  assert l->head == 1;
}
