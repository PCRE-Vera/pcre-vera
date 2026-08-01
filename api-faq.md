# APIs that did not behave the way we first assumed

Kept so the same surprise costs an hour once, not every time.

## `node --test <directory>` no longer scans the directory

Written as `node --test test/`, the way the Node documentation showed for
years. On Node 26 that fails with `Cannot find module '.../gen/js/test'`: a
positional argument is now resolved as a module path, not as a directory to
search.

The fix is to pass no path at all. `node --test` runs its own discovery from
the current directory, picking up `**/*.test.mjs` and friends and skipping
`node_modules`, which is what the directory argument was standing in for
anyway. The test script in `gen/js/package.json`, the `js` target in the
Makefile, and the CI job all use the bare form.

## `pcre2_config(PCRE2_CONFIG_VERSION, buf)` returns a length that includes the NUL

The obvious reading is that the return value is the string length, as with
`strlen`. It is one more than that: pcre2 counts the terminating NUL. Passing
the returned length straight to a hex encoder puts a stray `00` at the end of
every version string. The shim subtracts one, for `PCRE2_CONFIG_VERSION` and
`PCRE2_CONFIG_UNICODE_VERSION` alike.

## pcre2 compile error codes are offset by 100

The error numbering in `pcre2_error.c` starts at `ERR1`, so it is tempting to
expect `pcre2_compile` to report 14 for "missing closing parenthesis". It
reports 114: the public codes returned through `errorcodeptr` add
`COMPILE_ERROR_BASE`, which is 100. The seed corpus and, later, our own engine
speak the public numbering.

## `tarfile.extractall` needs `filter="data"` to be safe

Not a surprise so much as a version trap. The default filter changed to `data`
in Python 3.14; on 3.12 and 3.13, which this project still supports, the
default is the old permissive behavior that honours absolute paths, `..`
components, and device entries. Saying `filter="data"` outright means the same
policy on every supported version, which the oracle build does even though the
tarball it unpacks is hash-pinned.
