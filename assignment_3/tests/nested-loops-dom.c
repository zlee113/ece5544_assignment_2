int foo(int n)
{
    volatile int sum = 0;
    for (int i = 0; i < n; i++)
    {
        for (int j = 0; j < n; j++)
        {
            sum += i + j;
        }
    }
    return sum;
}