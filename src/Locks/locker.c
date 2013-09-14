#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/file.h>
#include <errno.h>

int debug(char* str) {
#ifdef DEBUG
    printf(str);
    printf("\n");
#endif
    return 0;
}

int get_path(char* buff, int id) {
    sprintf(buff, "/tmp/idris-resource-%d", id);
    return 0;
}

int open_file(int id) {
    int fd;
    char path[100];

    get_path(path, id);

    if ((fd = open(path, O_CREAT | O_RDWR, 0666)) < 0) {
        printf("Failed to open file");
        // can't be bothered to handle failure in Idris
        exit(EXIT_FAILURE);
    }
    return fd;
}

int init_lock(int id) {
    char path[100];
    get_path(path, id);
    remove(path);
    return 0;
}

int get_lock(int id) {
    int fd;
    fd = open_file(id);

    if (flock (fd, LOCK_EX) < 0) {
        printf("Locking failed");
        exit(EXIT_FAILURE);
    }
    debug("Got lock");
    return fd;
}

int release_lock(int fd) {
    debug("Released lock");
    flock(fd, LOCK_UN);
    close(fd);
    return 0;
}

int empty_file(int fd) {
    ftruncate(fd, 0);
    lseek(fd, 0, SEEK_SET);
    return 0;
}

int write_locked(int fd, int val) {
    debug("Writing...");
    empty_file(fd);
    char buf[100];
    sprintf(buf, "%d", val);
    debug(buf);
    write(fd, buf, strlen(buf));
    return 0;
}

int read_locked(int fd) {
    debug("Reading...");
    off_t size = lseek(fd, 0, SEEK_END);
    lseek(fd, 0, SEEK_SET);
    char *buff = malloc(size + 1);
    read(fd, buff, size);
    int ret;
    sscanf(buff, "%d", &ret);
    return ret;
}

