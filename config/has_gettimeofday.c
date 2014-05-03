#include <stddef.h>
#include <sys/time.h>
void main(void)
{
  static struct timeval tv0;
  if(!gettimeofday(&tv0, NULL))
    return 1;
  return 0;
}
