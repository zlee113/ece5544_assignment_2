int main(int argc, const char *argv[])
{
    int x = argc;
    int dead1 = x * 99;
    if (x > 0)
        x = x + 1;
    int dead2 = x * 88;
    return x;
}