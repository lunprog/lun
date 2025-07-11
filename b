#!/usr/bin/env python3

# Build system of the compiler
# TODO(URGENT): convert this to a cargo xtask
#
# Add the following to zshrc or bachrc to have the convenient `$ b` instead of
# `$ ./b`, or `$ ../b`
#
# b() {
#     local dir="$PWD"
#     local target="b"
#
#     while [ "$dir" != "/" ]; do
#         if [ -x "$dir/$target" ]; then
#             "$dir/$target" "$@"
#             return $?
#         elif [ -f "$dir/$target" ]; then
#             echo "Found '$target' at $dir/$target but it's not executable." >&2
#             return 126
#         fi
#         dir="$(dirname "$dir")"
#     done
#
#     echo "Error: '$target' not found in current or parent directories." >&2
#     return 127
# }

import subprocess as sp
import sys

def usage():
    return "Usage: ./b <command>, type help to see all the commands"

def main():
    args = sys.argv

    if len(args) <= 1:
        print(usage())
        return

    remaining_args = args[2:]
    match args[1]:
        case "lunc":
            cmd_lunc(remaining_args)
        case "test":
            cmd_test(remaining_args)
        case "build":
            cmd_build()
        case "watch":
            cmd_watch(remaining_args)
        case "help" | "h":
            cmd_help()
        case _:
            print(usage())
            return

def cmd_lunc(args: list[str]):
    # build
    res = build(True, "lunc")

    if res.returncode != 0:
        # compilation of lunc wasn't successful
        exit(res.returncode)

    # run
    run_cmd = ["target/debug/lunc"] + args
    res = sp.run(run_cmd)

    if res.returncode != 0:
        # subprocess wasn't successful
        exit(res.returncode)

def cmd_test(args: list[str]):
    # rebuild the compiler quietly, cargo will recompile only if something
    # changed
    res = build(True, "lunc")

    if res.returncode != 0:
        # compilation of lunc wasn't successful
        exit(res.returncode)

    # build
    res = build(True, "luntests")

    if res.returncode != 0:
        # compilation wasn't successful
        exit(res.returncode)

    # run
    run_cmd = ["target/debug/luntests"] + args
    res = sp.run(run_cmd)

    if res.returncode != 0:
        # tests were not successful
        exit(res.returncode)

def cmd_build():
    build(False, "lunc")

def build(quiet: bool, bin: str) -> any:
    args = []

    if quiet:
        args = ["cargo", "build", "-q", "--bin", bin]
    else:
        args = ["cargo", "build", "--bin", bin]

    return sp.run(args)

def cmd_watch(args: list[str]):
    if len(args) == 0:
        sp.run(["cargo", "watch"])
    else:
        cmd = ["cargo", "watch", "--shell", " ".join(args)]
        sp.run(cmd)

def cmd_help():
    print("""\
Build system for Lun compiler

Usage: ./b

Commands:
    build               Build the lun compiler
    watch [cmd]         Watch for changes in source code and runs [cmd] if
                        provided or defaults to `cargo check`
    lunc [ARGS...]      Runs the compiler with the given arguments, rebuild it
                        quietly if needed
    test [ARGS...]      Runs the compiler tests and forwards it the following
                        arguments
    help, h             Prints this message\
""")

if __name__ == "__main__":
    main()
