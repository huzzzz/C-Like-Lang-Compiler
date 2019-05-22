int *d;

int* f(int a, int b)
{
	int *c,m;
        c=&m;
	return c;
}


void main(){
	
	int x ,y, *px, *py;
        px = &x;
        py= &y;
        *px= 2;
        *py = 3;
	d = f(*px,*py);

}
