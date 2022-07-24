# Coq Installation Advice

> **Note**
> Coq and its standard library evolve with each release. The files in this
> repo have been tested against Coq 8.13.2, 8.14.1, and 8.15.2. YMMV with
> older or newer versions.

There are three main possibilities I suggest for installation:

- Use the Coq Scratchpad in your browser.

- Install Coq locally with Coq Platform, and use CoqIDE as your IDE.

- [more expertise required] Install Coq through OPAM, the OCaml Package Manager,
  and install either VS Code or Emacs as an IDE.

Below I provide advice about each of those possibilities.

## Coq Scratchpad

The easiest way to install Coq is to avoid installing it altogether! The
[jsCoq][jsCoq] project makes it possible run Coq entirely in your browser. For
at least the first chapter of the textbook, that's probably good enough. If
you're hooked after that, I recommend a local installation.

[jsCoq]: https://coq.vercel.app/

## Coq Platform

The primary way to install Coq locally is with the [Coq Platform][coq-platform]
distribution. It provides installation instructions for
[macOS][coq-platform-mac], [Windows][coq-platform-win], and
[Linux][coq-platform-linux].

[coq-platform]: https://github.com/coq/platform/blob/main/README.md
[coq-platform-mac]: https://github.com/coq/platform/blob/main/doc/README_macOS.md
[coq-platform-win]: https://github.com/coq/platform/blob/main/doc/README_Windows.md
[coq-platform-linux]: https://github.com/coq/platform/blob/main/doc/README_Linux.md

## Coq through OPAM

You might choose this option if you prefer to develop software from the terminal
with your choice of editor, such as VS Code or Emacs. Or, if you are already an
OCaml developer, you might prefer to use OPAM anyway. (Actually, Coq Platform
itself uses OPAM under the hood.)

**Step 1A. If you have NOT previously installed OPAM:** Follow the
[OPAM install instructions][opam-install].

[opam-install]: https://opam.ocaml.org/doc/Install.html

Then initialize OPAM:

```console
$ opam init
```

Now skip to Step 2.

**Step 1B. If you HAVE previously installed OPAM:** Take a moment to update its
package repository:

```console
$ opam update
```

When the update is done, it might prompt you to upgrade. It's up to you
whether you want to upgrade the packages in your current switch. We're
instead going to create a separate switch, next.

**Step 2. Create a switch for Software Foundations:** Run the following
commands. See the notes below them for some hints about troubleshooting and
options.

```console
$ opam switch create coq-sf ocaml-base-compiler.4.14.0
$ opam install utop
$ opam pin add coq 8.15.2
```

Notes:

- *Pinning* v8.15.2, as the last command above does, will ensure that OPAM does
  not try to upgrade it to a higher (possibly incompatible) version later.

- By create a new *switch*, we ensure Coq doesn't interfere with any other OCaml
  development you might do or have done in the past.

- Feel free to pick a different compiler version than 4.14.0. At the time of
  writing these notes, that was simply the most recent version.

- Feel free to pick a different switch name than `coq-sf`.

- If the `pin` command gives you an error because you are missing a library,
  install that library with your Unix package manager. The usual culprit seems
  to be the GNU Multiple Precision Arithmetic library.

**Step 3. Check that Coq is working.** The Coq *toplevel* is `coqtop`. Here is a
sample interaction:

```console
$ coqtop
Welcome to Coq 8.15.2

Coq < Check true.
true
        : bool

Coq < Quit.
```

Next you need to install an IDE. There are two main options: VS Code and Proof
General.

**Step 4A. Install VS Code.**

(Or skip to step 4B.)

Install [Visual Studio Code][vsc-install], then install the VSCoq extension by
Maxime Dénès. Optionally you can also install the Prettify Symbols Mode
extension by siegebell.

[vsc-install]: https://code.visualstudio.com/

> **Warning:**
> When you edit Coq source files with VS Code, you should make sure that you
> open the *directory* the file is in, rather than opening the *file* itself.
> For example, if `foo.v` is a file in the current working directory, open it
> with `code .` not `code foo.v`. This is necessary to make sure that other
> files in the same directory can be imported by `foo`.

**Step 4B. Install Proof General.**

Proof General is a plugin for Emacs. Note that you can use
[Evil mode][evil-mode] to get Vim keybindings, if you prefer those.

- Install [Emacs][emacs]. If you're new to Emacs, start by doing the built-in
  tutorial with `C-h t`. That is, `Control-h` followed by `t`. It will take
  maybe an hour.

- Install Proof General and Company Coq (which is an extension of Proof General
  for Coq) by following [these instructions][company-coq]. The Company Coq
  tutorial, mentioned at the end of those instructions, might not make much
  sense yet. It assumes you know Coq already.

- You can double check that Proof General is working correctly as follows. Visit
  a new Coq file in Emacs with `C-x C-f test.v`. Enter this code: `Check true.`
  Press `C-c C-n` to compile it. You should get the output `true : bool` in the
  Coq Response window. In a correctly configured GUI Emacs you will see &Bopf;
  instead of `bool`.

[evil-mode]: https://evil.readthedocs.io/en/latest/overview.html#installation-via-package-el
[emacs]: https://www.gnu.org/software/emacs/download.html
[company-coq]: https://github.com/cpitclaudel/company-coq#setup
 
