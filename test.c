#include <stdio.h>

static int is_prime(unsigned int n) {
  int i;
  //printf("checking %d\n", n);
  for(int i = 2; i*i <= n; i++) {
    if(n % i == 0) {return 0;}
  }
  return 1;
}


int main(void) {
    for(int i =100000; i<1000000; i++){
        if (is_prime(i)){
            return i;
        }
    }
    return -1;
}
