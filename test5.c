
#include <stdio.h>

int main()
{
	int i;
	int b[10];
	int a[10];
	for(i = 3; i < 10; i++)
	{
		a[i] = a[i-3];
		b[i] = b[i-2];
	}
	return 0;
}
