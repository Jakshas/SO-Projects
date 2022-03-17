#ifdef READLINE
#include <readline/readline.h>
#include <readline/history.h>
#endif

#define DEBUG 0
#include "shell.h"

sigset_t sigchld_mask;

static void sigint_handler(int sig) {
  /* No-op handler, we just need break read() call with EINTR. */
  (void)sig;
}

/* Rewrite closed file descriptors to -1,
 * to make sure we don't attempt do close them twice. */
static void MaybeClose(int *fdp) {
  if (*fdp < 0)
    return;
  Close(*fdp);
  *fdp = -1;
}

/* Consume all tokens related to redirection operators.
 * Put opened file descriptors into inputp & output respectively. */
static int do_redir(token_t *token, int ntokens, int *inputp, int *outputp) {
  token_t mode = NULL; /* T_INPUT, T_OUTPUT or NULL */
  int n = 0;           /* number of tokens after redirections are removed */

  for (int i = 0; i < ntokens; i++) {
    /* TODO: Handle tokens and open files as requested. */
#ifdef STUDENT
    mode = token[i];
    n++;
    // jesli nie flaga dodaj 1 do ilosci tokenów
    if (mode == T_INPUT) {
      // msg("|%s|",mode);
      // Zamkniecie otwartego fd
      MaybeClose(inputp);
      *inputp = Open(token[i + 1], O_RDONLY, 0); // czytaj
      i++; // pomin nastepny bo to bedzie io
      n = n - 1;
    } else if (mode == T_OUTPUT) {
      // msg("|%s|",mode);
      // Zamkniecie otwartego fd
      MaybeClose(outputp);
      *outputp = Open(
        token[i + 1], O_WRONLY | O_CREAT,
        S_IRWXU | S_IRWXG |
          S_IRWXO); // otwóż do odczytu jak nie ma utówrz nowy z uprawnieniami
      i++;          // pomin nastepny bo to bedzie io
      n = n - 1;
    }
#endif /* !STUDENT */
  }

  token[n] = NULL;
  return n;
}

/* Execute internal command within shell's process or execute external command
 * in a subprocess. External command can be run in the background. */
static int do_job(token_t *token, int ntokens, bool bg) {
  int input = -1, output = -1;
  int exitcode = 0;

  ntokens = do_redir(token, ntokens, &input, &output);

  if (!bg) {
    if ((exitcode = builtin_command(token)) >= 0)
      return exitcode;
  }

  sigset_t mask;
  Sigprocmask(SIG_BLOCK, &sigchld_mask, &mask);

  /* TODO: Start a subprocess, create a job and monitor it. */
#ifdef STUDENT
  pid_t pid = Fork();
  // ustawienie pgid dziecka w rodzicu i dziecku
  setpgid(pid, pid);
  // jesli dziecko
  if (pid == 0) {
    // ustaw flagi takie jak w mainie
    Signal(SIGTSTP, SIG_DFL);
    Signal(SIGTTIN, SIG_DFL);
    Signal(SIGTTOU, SIG_DFL);
    Sigprocmask(SIG_SETMASK, &mask, NULL);
    // kopiuj deskryptory
    if (input != -1) {
      Dup2(input, STDIN_FILENO);
      Close(input);
    }
    if (output != -1) {
      Dup2(output, STDOUT_FILENO);
      Close(output);
    }
    // wykonaj
    external_command(token);
  }
  // zamknij deskryptory
  MaybeClose(&input);
  MaybeClose(&output);
  // doda joba i go monitoruj jesli fg
  int job = addjob(pid, bg);
  addproc(job, pid, token);
  if (bg) {
    msg("[%d] running '%s'\n", job, jobcmd(job));
  } else {
    exitcode = monitorjob(&mask);
  }

#endif /* !STUDENT */

  Sigprocmask(SIG_SETMASK, &mask, NULL);
  return exitcode;
}

/* Start internal or external command in a subprocess that belongs to pipeline.
 * All subprocesses in pipeline must belong to the same process group. */
static pid_t do_stage(pid_t pgid, sigset_t *mask, int input, int output,
                      token_t *token, int ntokens, bool bg) {
  ntokens = do_redir(token, ntokens, &input, &output);

  if (ntokens == 0)
    app_error("ERROR: Command line is not well formed!");

  /* TODO: Start a subprocess and make sure it's moved to a process group. */
  pid_t pid = Fork();
#ifdef STUDENT
  // ustawienie pgid w rodzicu i dziecku
  int exitcode;
  setpgid(pid, pgid);
  // jesli dziecko
  if (pid == 0) {
    // maski z maina
    Signal(SIGTSTP, SIG_DFL);
    Signal(SIGTTIN, SIG_DFL);
    Signal(SIGTTOU, SIG_DFL);
    Sigprocmask(SIG_SETMASK, mask, NULL);
    // jesli komenda to wykonaj
    if ((exitcode = builtin_command(token)) >= 0)
      exit(exitcode);
    // przekieruj wejscie wyjscie
    if (input != -1) {
      Dup2(input, STDIN_FILENO);
      Close(input);
    }
    if (output != -1) {
      Dup2(output, STDOUT_FILENO);
      Close(output);
    }

    external_command(token);
  }

#endif /* !STUDENT */

  return pid;
}

static void mkpipe(int *readp, int *writep) {
  int fds[2];
  Pipe(fds);
  fcntl(fds[0], F_SETFD, FD_CLOEXEC);
  fcntl(fds[1], F_SETFD, FD_CLOEXEC);
  *readp = fds[0];
  *writep = fds[1];
}

/* Pipeline execution creates a multiprocess job. Both internal and external
 * commands are executed in subprocesses. */
static int do_pipeline(token_t *token, int ntokens, bool bg) {
  pid_t pid, pgid = 0;
  int job = -1;
  int exitcode = 0;

  int input = -1, output = -1, next_input = -1;

  mkpipe(&next_input, &output);

  sigset_t mask;
  Sigprocmask(SIG_BLOCK, &sigchld_mask, &mask);

  /* TODO: Start pipeline subprocesses, create a job and monitor it.
   * Remember to close unused pipe ends! */
#ifdef STUDENT
  // wskazniki na elementy
  int begin = 0;
  int end;

  while (begin < ntokens) {
    // znajdz nastepny pipe
    for (end = begin; end != ntokens && token[end] != T_PIPE; end++)
      ;
    // zrób nowego pipa miedzy kolejnymi czesciami albo podpiecie inputu
    if (begin != 0) {
      input = next_input;
      if (end != ntokens) {
        mkpipe(&next_input, &output);
      }
    }
    // wykonaj program
    pid = do_stage(pgid, &mask, input, output, token + begin, end - begin, bg);
    // pozamykaj fd
    MaybeClose(&input);
    MaybeClose(&output);
    // ustawienie pgid pierwszego w grupie
    if (pgid == 0) {
      pgid = pid;
      job = addjob(pid, bg);
    }
    // dodanie porcesu
    addproc(job, pid, token + begin);
    // przechodznie do nastepnego
    begin = end + 1;
  }

  // monitoruj jesli fg
  if (!bg) {
    exitcode = monitorjob(&mask);
  } else {
    msg("[%d] running '%s'\n", job, jobcmd(job));
  }

#endif /* !STUDENT */

  Sigprocmask(SIG_SETMASK, &mask, NULL);
  return exitcode;
}

static bool is_pipeline(token_t *token, int ntokens) {
  for (int i = 0; i < ntokens; i++)
    if (token[i] == T_PIPE)
      return true;
  return false;
}

static void eval(char *cmdline) {
  bool bg = false;
  int ntokens;
  token_t *token = tokenize(cmdline, &ntokens);

  if (ntokens > 0 && token[ntokens - 1] == T_BGJOB) {
    token[--ntokens] = NULL;
    bg = true;
  }

  if (ntokens > 0) {
    if (is_pipeline(token, ntokens)) {
      do_pipeline(token, ntokens, bg);
    } else {
      do_job(token, ntokens, bg);
    }
  }

  free(token);
}

#ifndef READLINE
static char *readline(const char *prompt) {
  static char line[MAXLINE]; /* `readline` is clearly not reentrant! */

  write(STDOUT_FILENO, prompt, strlen(prompt));

  line[0] = '\0';

  ssize_t nread = read(STDIN_FILENO, line, MAXLINE);
  if (nread < 0) {
    if (errno != EINTR)
      unix_error("Read error");
    msg("\n");
  } else if (nread == 0) {
    return NULL; /* EOF */
  } else {
    if (line[nread - 1] == '\n')
      line[nread - 1] = '\0';
  }

  return strdup(line);
}
#endif

int main(int argc, char *argv[]) {
  /* `stdin` should be attached to terminal running in canonical mode */
  if (!isatty(STDIN_FILENO))
    app_error("ERROR: Shell can run only in interactive mode!");

#ifdef READLINE
  rl_initialize();
#endif

  sigemptyset(&sigchld_mask);
  sigaddset(&sigchld_mask, SIGCHLD);

  if (getsid(0) != getpgid(0))
    Setpgid(0, 0);

  initjobs();

  struct sigaction act = {
    .sa_handler = sigint_handler,
    .sa_flags = 0, /* without SA_RESTART read() will return EINTR */
  };
  Sigaction(SIGINT, &act, NULL);

  Signal(SIGTSTP, SIG_IGN);
  Signal(SIGTTIN, SIG_IGN);
  Signal(SIGTTOU, SIG_IGN);

  while (true) {
    char *line = readline("# ");

    if (line == NULL)
      break;

    if (strlen(line)) {
#ifdef READLINE
      add_history(line);
#endif
      eval(line);
    }
    free(line);
    watchjobs(FINISHED);
  }

  msg("\n");
  shutdownjobs();

  return 0;
}
