#!/usr/bin/env python3
#
# Build system of the compiler

import subprocess as sp
import sys

def usage():
    return "Usage: ./b <command>, type help to see all the commands"

def main():
    args = sys.argv

    if len(args) <= 1:
        print(usage())
        return

    match args[1]:
        case "lunc":
            cmd_lunc(args[2:])
        case "build":
            cmd_build()
        case "watch":
            cmd_watch()
        case "help" | "h":
            cmd_help()
        case _:
            print(usage())
            return

def cmd_lunc(args: list[str]):
    # build
    sp.run(["cargo", "build", "-q"])
    build(True)

    # run
    run_cmd = ["target/debug/lunc"] + args
    sp.run(run_cmd)

def cmd_build():
    build(False)

def build(quiet: bool):
    args = []

    if quiet:
        args = ["cargo", "build", "-q"]
    else:
        args = ["cargo", "build"]

    sp.run(args)

def cmd_watch():
    sp.run(["cargo", "watch"])

def cmd_help():
    print("""\
Build system for Lun compiler

Usage: ./b

Commands:
    build               Build the lun compiler
    watch               Watch for changes in source code and runs `cargo check`
                        if changes were made
    lunc [ARGS...]      Runs the compiler with the given arguments, rebuild it
                        quietly if needed
    help, h             Prints this message\
""")

if __name__ == "__main__":
    main()
