#include "elfloader.h"
#include <stdio.h>
#include <stdlib.h>
#include <elf.h>
#include <sys/mman.h>
#include <string.h>

#define STRINGIZE(x) STRINGIZE2(x)
#define STRINGIZE2(x) #x
#define FILE_LINE(n) (__FILE__ " L" STRINGIZE(__LINE__) " " n)

void elf_init(elf_t *elf, const char *elf_path) {
  FILE *fp = NULL;
  Elf32_Ehdr *elf_header;
  // read headers
  if ((fp = fopen(elf_path, "r")) == NULL) {
    perror(FILE_LINE("fopen"));
    goto cleanup;
  }
  fstat(fileno(fp), &elf->file_stat);
  elf->head = (char *)mmap(NULL, elf->file_stat.st_size, PROT_READ, MAP_PRIVATE, fileno(fp), 0);
  if (elf->head == MAP_FAILED) {
    perror(FILE_LINE("mmap"));
    goto cleanup;
  }
  // elf header
  elf_header = (Elf32_Ehdr *)elf->head;
  // set program entry address
  elf->entry_address = elf_header->e_entry;

  // set programs
  elf->programs = 0;
  elf->program_size = NULL;
  elf->program = NULL;
  elf->program_base = NULL;
  for (int i = 0; i < elf_header->e_shnum; i++) {
    Elf32_Shdr *shstrtab = (Elf32_Shdr *)(&elf->head[elf_header->e_shoff + elf_header->e_shentsize * elf_header->e_shstrndx]);
    Elf32_Shdr *sh = (Elf32_Shdr *)(&elf->head[elf_header->e_shoff + elf_header->e_shentsize * i]);
    if (strncmp(".text", &elf->head[shstrtab->sh_offset + sh->sh_name], 16) == 0) {
      elf->program_size = (unsigned *)realloc(elf->program_size, (elf->programs + 1) * sizeof(unsigned));
      elf->program_size[elf->programs] = sh->sh_size;
      elf->program_base = (unsigned *)realloc(elf->program_base, (elf->programs + 1) * sizeof(unsigned));
      elf->program_base[elf->programs] = 0;
      elf->program = (char **)realloc(elf->program, (elf->programs + 1) * sizeof(char *));
      elf->program[elf->programs] = &(elf->head[sh->sh_offset]);
      elf->programs++;
    }
  }
 cleanup:
  fclose(fp);
  return;
}

void elf_fini(elf_t *elf) {
  munmap(elf->head, elf->file_stat.st_size);
  free(elf->program);
  free(elf->program_size);
  free(elf->program_base);
  return;
}
