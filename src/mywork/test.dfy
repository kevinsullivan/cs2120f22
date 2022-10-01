function method fib(n: nat): nat
{
    if (n < 2) then n
    else fib(n-2) + fib(n-1)
}

method Main()
{
    print("The 20th Fibonacci number is ");
    print(fib(20));
    print("\n");
}

