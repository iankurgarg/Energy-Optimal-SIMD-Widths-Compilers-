
#include <stdio.h>

int main()
{
	int i;
	int b[10];
	int a[10];
	for(i = 3; i < 10; i++)
	{
		a[i] = b[i-1] + a[i-1];
	}
	return 0;
}
