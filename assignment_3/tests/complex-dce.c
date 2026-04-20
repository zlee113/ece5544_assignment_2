int main(int argc, const char *argv[])
{
    int x = 1;
    int a = x + 50;
    int b = a + 96;
    int c;
    int d;
    if (a > 50)
    {
        c = a - 50;
        d = a + 96;
    }
    else
    {
        c = a + 50;
        d = a - 96;
    }
    int e = 50 - 96;
    int f = e + c;
    return f;
}