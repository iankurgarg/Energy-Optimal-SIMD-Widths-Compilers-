#include <stdio.h>

int main()
{
	int i;
	int b[10];
	int a[10];
	for(i = 3; i < 10; i++)
	{
		a[i] = b[i] + a[i-2] + a[i-3];
	}
	return 0;
}
