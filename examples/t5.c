int *d;

int* f(int a, int c)
{
	int *b,l;
	b=&l;
	return b;
}


void main(){
	
	int x ,*ptr;
	ptr=&x;
	*ptr =9;
	if(*ptr>5){
		d = f(3,*ptr);
	}
}
