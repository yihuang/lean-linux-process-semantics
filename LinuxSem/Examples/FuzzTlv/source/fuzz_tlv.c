/* fuzz_tlv.c: a fuzz target and its driver, freestanding, for riscv64 Linux.
 *
 * The target walks records [tag:u8][len:u8][value:len bytes] and sums the
 * value bytes.  The driver reads standard input into a buffer whose last byte
 * is the last byte the image maps, then calls the target on what it read,
 * after the 6-byte header a driver file carries.
 *
 * Built without FIXED this file has the bugs the proof is about: the driver
 * does not reject an input shorter than the header, so `size` underflows, and
 * the target trusts `len`.  Both reach the end of the mapping and fault.
 */
typedef unsigned char u8;
typedef unsigned long usize;

#define PAGE_SIZE 4096
#define BUF_SIZE 256
#define HEADER 6
#define EXIT_OK 0
#define EXIT_REFUSED 2
#define EXIT_BAD_RETURN 78

/* The last page the image maps.  `input` is its last BUF_SIZE bytes, so the
 * first byte past the buffer is not mapped: an out-of-bounds read faults, in
 * the plain build, with no sanitizer involved. */
static u8 last_page[PAGE_SIZE] __attribute__((aligned(PAGE_SIZE)));
#define input (last_page + PAGE_SIZE - BUF_SIZE)

static inline long sys3(long n, long a, long b, long c) {
  register long a0 __asm__("a0") = a;
  register long a1 __asm__("a1") = b;
  register long a2 __asm__("a2") = c;
  register long a7 __asm__("a7") = n;
  __asm__ volatile("ecall" : "+r"(a0) : "r"(a1), "r"(a2), "r"(a7) : "memory");
  return a0;
}

__attribute__((noreturn)) static inline void sys_exit(long code) {
  sys3(94, code, 0, 0);
  __builtin_unreachable();
}

__attribute__((noinline)) int LLVMFuzzerTestOneInput(const u8 *data, usize size) {
  usize off = 0;
  unsigned sum = 0;
  while (size - off >= 2) {
    usize len = data[off + 1];
    off += 2;
#ifdef FIXED
    if (len > size - off) return -1;
#endif
    for (usize i = 0; i < len; i++) sum += data[off + i];
    off += len;
  }
  return sum == 0xdeadbeef ? -1 : 0;
}

__attribute__((noreturn)) void _start(void) {
  usize n = 0;
  for (;;) {
    long r = sys3(63, 0, (long)(input + n), BUF_SIZE - n);
    if (r < 0) sys_exit(EXIT_REFUSED);
    if (r == 0) break;
    n += (usize)r;
    if (n == BUF_SIZE) sys_exit(EXIT_REFUSED);
  }
#ifdef FIXED
  if (n < HEADER) sys_exit(EXIT_REFUSED);
#endif
  int rc = LLVMFuzzerTestOneInput(input + HEADER, n - HEADER);
  sys_exit(rc == 0 || rc == -1 ? EXIT_OK : EXIT_BAD_RETURN);
}
