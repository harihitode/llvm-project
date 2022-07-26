#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include "sim.h"

sig_atomic_t quit = 0;

void shndl(int signum) {
  if (signum == SIGINT) {
    quit = 1;
  }
}

void callback(sim_t *sim) {
  unsigned trap_code = sim_get_trap_code(sim);
  switch (trap_code) {
  case TRAP_CODE_ILLEGAL_INSTRUCTION:
    fprintf(stderr, "ILLEGAL INSTRUCTION\n");
    quit = 1;
    break;
  case TRAP_CODE_BREAKPOINT:
    quit = 1;
    break;
  default:
    break;
  }
  return;
}

int main(int argc, char *argv[]) {
  int entry_args[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  if (argc < 2) {
    fprintf(stderr, "%s [ELF FILE]\n", argv[0]);
    return 0;
  }
  for (int i = 2; i < (argc > 10 ? 10 : argc); i++) {
    entry_args[i - 2] = atoi(argv[i]);
  }
  FILE *fp = fopen(argv[1], "r");
  if (fp == NULL) {
    perror("fopen");
    return 0;
  }
  fclose(fp);
  sim_t *sim;
  sim = (sim_t *)malloc(sizeof(sim_t));
  sim_init(sim, argv[1]);
  // set entry function
  for (int i = 0; i < 8; i++) {
    sim_write_register(sim, 10 + i, entry_args[i]);
  }
  // set stack pointer
  sim_write_register(sim, 2, 0x00001000);
  // set simulation trap
  sim_trap(sim, callback);
  signal(SIGINT, shndl);
  // main loop
  while (quit == 0) {
    sim_step(sim);
  }
  fprintf(stderr, "simulation end @ PC:%08x, INST:%08x\n", sim->pc, sim_read_memory(sim, sim->pc));
  fprintf(stderr, "RESULT: %08x\n", sim_read_register(sim, 10));
  sim_fini(sim);
  free(sim);
  return 0;
}
