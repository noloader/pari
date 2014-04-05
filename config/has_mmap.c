#include <unistd.h>
#include <sys/mman.h>
int main(void)
{
  size_t size = sysconf(_SC_PAGE_SIZE)*1000;
  void *b = mmap(NULL, size, PROT_READ|PROT_WRITE,
                             MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE,-1,0);
  madvise(b, size, MADV_DONTNEED);
  munmap(b, size);
  return 0;
}
