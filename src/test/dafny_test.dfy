module dafny_test {
    function method sqr(n : nat) : nat { n * n }

    method Main() {
        print("Hello world!\n");
        print("By the way, the square of 5 is ", sqr(5), "\n");
    }
}
