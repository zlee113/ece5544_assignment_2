int main()
{
    int a = 5;
    int b = 3;
    int result = 0;
    for (int i = 0; i < 10; i++)
    {
        int x = a + b;
        int y = x * 2;
        result += y;
    }
    return result;
}