// Force a second HYDRA split on a call reached through the later goto target.
var g: int;

procedure {:entrypoint} main() {
  g := 0;
  goto First, Later;

First:
  call warmup();
  return;

Later:
  g := 1;
  call check();
  return;
}

procedure warmup() {
  assert true;
}

procedure check() {
  call depth1();
}

procedure depth1() {
  call depth2();
}

procedure depth2() {
  call depth3();
}

procedure depth3() {
  assert g == 0;
}
