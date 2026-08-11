procedure {:entrypoint} main() {
  call mid();
}
procedure mid() {
  call leaf_ok();
  call leaf_bug();
}
procedure leaf_ok() { assert true; }
procedure leaf_bug() { assert false; }
