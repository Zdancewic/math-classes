###############################################################################
##  v      #                   The Coq Proof Assistant                       ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                   ##
##   \VV/  #                                                                 ##
##    //   #                                                                 ##
###############################################################################
## GNUMakefile for Coq 8.8.0

# For debugging purposes (must stay here, don't move below)
INITIAL_VARS := $(.VARIABLES)
# To implement recursion we save the name of the main Makefile
SELF := $(lastword $(MAKEFILE_LIST))
PARENT := $(firstword $(MAKEFILE_LIST))

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject:
	./configure.sh

# Put in place old names
VFILES            := $(COQMF_VFILES)
MLIFILES          := $(COQMF_MLIFILES)
MLFILES           := $(COQMF_MLFILES)
ML4FILES          := $(COQMF_ML4FILES)
MLPACKFILES       := $(COQMF_MLPACKFILES)
MLLIBFILES        := $(COQMF_MLLIBFILES)
CMDLINE_VFILES    := $(COQMF_CMDLINE_VFILES)
INSTALLCOQDOCROOT := $(COQMF_INSTALLCOQDOCROOT)
OTHERFLAGS        := $(COQMF_OTHERFLAGS)
COQ_SRC_SUBDIRS   := $(COQMF_COQ_SRC_SUBDIRS)
OCAMLLIBS         := $(COQMF_OCAMLLIBS)
SRC_SUBDIRS       := $(COQMF_SRC_SUBDIRS)
COQLIBS           := $(COQMF_COQLIBS)
COQLIBS_NOML      := $(COQMF_COQLIBS_NOML)
CMDLINE_COQLIBS   := $(COQMF_CMDLINE_COQLIBS)
LOCAL             := $(COQMF_LOCAL)
COQLIB            := $(COQMF_COQLIB)
DOCDIR            := $(COQMF_DOCDIR)
OCAMLFIND         := $(COQMF_OCAMLFIND)
CAMLP5O           := $(COQMF_CAMLP5O)
CAMLP5BIN         := $(COQMF_CAMLP5BIN)
CAMLP5LIB         := $(COQMF_CAMLP5LIB)
CAMLP5OPTIONS     := $(COQMF_CAMLP5OPTIONS)
CAMLFLAGS         := $(COQMF_CAMLFLAGS)
HASNATDYNLINK     := $(COQMF_HASNATDYNLINK)

Makefile.conf: Make
	coq_makefile -f Make -o Makefile

# This file can be created by the user to hook into double colon rules or
# add any other Makefile code he may need
-include Makefile.local

# Parameters ##################################################################
#
# Parameters are make variable assignments.
# They can be passed to (each call to) make on the command line.
# They can also be put in Makefile.local once an for all.
# For retro-compatibility reasons they can be put in the _CoqProject, but this
# practice is discouraged since _CoqProject better not contain make specific
# code (be nice to user interfaces).

# Print shell commands (set to non empty)
VERBOSE ?=

# Time the Coq process (set to non empty), and how (see default value)
TIMED?=
TIMECMD?=
# Use /usr/bin/env time on linux, gtime on Mac OS
TIMEFMT?="$* (real: %e, user: %U, sys: %S, mem: %M ko)"
ifneq (,$(TIMED))
ifeq (0,$(shell /usr/bin/env time -f $(TIMEFMT) true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=/usr/bin/env time -f $(TIMEFMT)
else
ifeq (0,$(shell gtime -f $(TIMEFMT) true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=gtime -f $(TIMEFMT)
else
STDTIME?=time
endif
endif
else
STDTIME?=/usr/bin/env time -f $(TIMEFMT)
endif

# Coq binaries
COQC     ?= "$(COQBIN)coqc"
COQTOP   ?= "$(COQBIN)coqtop"
COQCHK   ?= "$(COQBIN)coqchk"
COQDEP   ?= "$(COQBIN)coqdep"
GALLINA  ?= "$(COQBIN)gallina"
COQDOC   ?= "$(COQBIN)coqdoc"
COQMKFILE ?= "$(COQBIN)coq_makefile"

# Timing scripts
COQMAKE_ONE_TIME_FILE ?= "$(COQLIB)/tools/make-one-time-file.py"
COQMAKE_BOTH_TIME_FILES ?= "$(COQLIB)/tools/make-both-time-files.py"
COQMAKE_BOTH_SINGLE_TIMING_FILES ?= "$(COQLIB)/tools/make-both-single-timing-files.py"
BEFORE ?=
AFTER ?=

# FIXME this should be generated by Coq (modules already linked by Coq)
CAMLDONTLINK=camlp5.gramlib,unix,str

# OCaml binaries
CAMLC       ?= "$(OCAMLFIND)" ocamlc   -c
CAMLOPTC    ?= "$(OCAMLFIND)" opt      -c
CAMLLINK    ?= "$(OCAMLFIND)" ocamlc   -linkpkg -dontlink $(CAMLDONTLINK)
CAMLOPTLINK ?= "$(OCAMLFIND)" opt      -linkpkg -dontlink $(CAMLDONTLINK)
CAMLDOC     ?= "$(OCAMLFIND)" ocamldoc
CAMLDEP     ?= "$(OCAMLFIND)" ocamldep -slash -ml-synonym .ml4 -ml-synonym .mlpack

# DESTDIR is prepended to all installation paths
DESTDIR ?=

# Debug builds, typically -g to OCaml, -debug to Coq.
CAMLDEBUG ?=
COQDEBUG ?=

# Extra packages to be linked in (as in findlib -package)
CAMLPKGS ?=

# Option for making timing files
TIMING?=
# Option for changing sorting of timing output file
TIMING_SORT_BY ?= auto
# Output file names for timed builds
TIME_OF_BUILD_FILE               ?= time-of-build.log
TIME_OF_BUILD_BEFORE_FILE        ?= time-of-build-before.log
TIME_OF_BUILD_AFTER_FILE         ?= time-of-build-after.log
TIME_OF_PRETTY_BUILD_FILE        ?= time-of-build-pretty.log
TIME_OF_PRETTY_BOTH_BUILD_FILE   ?= time-of-build-both.log
TIME_OF_PRETTY_BUILD_EXTRA_FILES ?= - # also output to the command line

########## End of parameters ##################################################
# What follows may be relevant to you only if you need to
# extend this Makefile.  If so, look for 'Extension point' here and
# put in Makefile.local double colon rules accordingly.
# E.g. to perform some work after the all target completes you can write
#
# post-all::
# 	echo "All done!"
#
# in Makefile.local
#
###############################################################################




# Flags #######################################################################
#
# We define a bunch of variables combining the parameters

SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

OPT?=

# The DYNOBJ and DYNLIB variables are used by "coqdep -dyndep var" in .v.d
ifeq '$(OPT)' '-byte'
USEBYTE:=true
DYNOBJ:=.cma
DYNLIB:=.cma
else
USEBYTE:=
DYNOBJ:=.cmxs
DYNLIB:=.cmxs
endif

COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS)
COQCHKFLAGS?=-silent -o $(COQLIBS)
COQDOCFLAGS?=-interpolate -utf8
COQDOCLIBS?=$(COQLIBS_NOML)

# The version of Coq being run and the version of coq_makefile that
# generated this makefile
COQ_VERSION:=$(shell $(COQC) --print-version | cut -d " " -f 1)
COQMAKEFILE_VERSION:=8.8.0

COQSRCLIBS?= $(foreach d,$(COQ_SRC_SUBDIRS), -I "$(COQLIB)$(d)")

CAMLFLAGS+=$(OCAMLLIBS) $(COQSRCLIBS) -I $(CAMLP5LIB)

# ocamldoc fails with unknown argument otherwise
CAMLDOCFLAGS=$(filter-out -annot, $(filter-out -bin-annot, $(CAMLFLAGS)))

# FIXME This should be generated by Coq
GRAMMARS:=grammar.cma
CAMLP5EXTEND=pa_extend.cmo q_MLast.cmo pa_macro.cmo

CAMLLIB:=$(shell "$(OCAMLFIND)" printconf stdlib 2> /dev/null)
ifeq (,$(CAMLLIB))
PP=$(error "Cannot find the 'ocamlfind' binary used to build Coq ($(OCAMLFIND)). Pre-compiled binary packages of Coq do not support compiling plugins this way. Please download the sources of Coq and run the Windows build script.")
else
PP:=-pp '$(CAMLP5O) -I $(CAMLLIB) -I "$(COQLIB)/grammar" $(CAMLP5EXTEND) $(GRAMMARS) $(CAMLP5OPTIONS) -impl'
endif

ifneq (,$(TIMING))
TIMING_ARG=-time
ifeq (after,$(TIMING))
TIMING_EXT=after-timing
else
ifeq (before,$(TIMING))
TIMING_EXT=before-timing
else
TIMING_EXT=timing
endif
endif
else
TIMING_ARG=
endif

# Retro compatibility (DESTDIR is standard on Unix, DSTROOT is not)
ifdef DSTROOT
DESTDIR := $(DSTROOT)
endif

concat_path = $(if $(1),$(1)/$(subst $(COQMF_WINDRIVE),/,$(2)),$(2))

COQLIBINSTALL = $(call concat_path,$(DESTDIR),$(COQLIB)user-contrib)
COQDOCINSTALL = $(call concat_path,$(DESTDIR),$(DOCDIR)user-contrib)
COQTOPINSTALL = $(call concat_path,$(DESTDIR),$(COQLIB)toploop)

# Files #######################################################################
#
# We here define a bunch of variables about the files being part of the
# Coq project in order to ease the writing of build target and build rules

VDFILE := .coqdeps

ALLSRCFILES := \
	$(ML4FILES) \
	$(MLFILES) \
	$(MLPACKFILES) \
	$(MLLIBFILES) \
	$(MLIFILES)

# helpers
vo_to_obj = $(addsuffix .o,\
  $(filter-out Warning: Error:,\
  $(shell $(COQTOP) -q -noinit -batch -quiet -print-mod-uid $(1))))
strip_dotslash = $(patsubst ./%,%,$(1))
VO = vo

VOFILES = $(VFILES:.v=.$(VO))
GLOBFILES = $(VFILES:.v=.glob)
GFILES = $(VFILES:.v=.g)
HTMLFILES = $(VFILES:.v=.html)
GHTMLFILES = $(VFILES:.v=.g.html)
BEAUTYFILES = $(addsuffix .beautified,$(VFILES))
TEXFILES = $(VFILES:.v=.tex)
GTEXFILES = $(VFILES:.v=.g.tex)
CMOFILES = \
	$(ML4FILES:.ml4=.cmo) \
	$(MLFILES:.ml=.cmo) \
	$(MLPACKFILES:.mlpack=.cmo)
CMXFILES = $(CMOFILES:.cmo=.cmx)
OFILES = $(CMXFILES:.cmx=.o)
CMAFILES = $(MLLIBFILES:.mllib=.cma) $(MLPACKFILES:.mlpack=.cma)
CMXAFILES = $(CMAFILES:.cma=.cmxa)
CMIFILES = \
	$(CMOFILES:.cmo=.cmi) \
	$(MLIFILES:.mli=.cmi)
# the /if/ is because old _CoqProject did not list a .ml(pack|lib) but just
# a .ml4 file
CMXSFILES = \
	$(MLPACKFILES:.mlpack=.cmxs) \
	$(CMXAFILES:.cmxa=.cmxs) \
	$(if $(MLPACKFILES)$(CMXAFILES),,\
		$(ML4FILES:.ml4=.cmxs) $(MLFILES:.ml=.cmxs))

# files that are packed into a plugin (no extension)
PACKEDFILES = \
	$(call strip_dotslash, \
	  $(foreach lib, \
            $(call strip_dotslash, \
	       $(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES)),$($(lib))))
# files that are archived into a .cma (mllib)
LIBEDFILES = \
	$(call strip_dotslash, \
	  $(foreach lib, \
            $(call strip_dotslash, \
	       $(MLLIBFILES:.mllib=_MLLIB_DEPENDENCIES)),$($(lib))))
CMIFILESTOINSTALL = $(filter-out $(addsuffix .cmi,$(PACKEDFILES)),$(CMIFILES))
CMOFILESTOINSTALL = $(filter-out $(addsuffix .cmo,$(PACKEDFILES)),$(CMOFILES))
OBJFILES = $(call vo_to_obj,$(VOFILES))
ALLNATIVEFILES = \
	$(OBJFILES:.o=.cmi) \
	$(OBJFILES:.o=.cmx) \
	$(OBJFILES:.o=.cmxs)
# trick: wildcard filters out non-existing files, so that `install` doesn't show
# warnings and `clean` doesn't pass to rm a list of files that is too long for
# the shell.
NATIVEFILES = $(wildcard $(ALLNATIVEFILES))
FILESTOINSTALL = \
	$(VOFILES) \
	$(VFILES) \
	$(GLOBFILES) \
	$(NATIVEFILES) \
	$(CMIFILESTOINSTALL)
BYTEFILESTOINSTALL = \
	$(CMOFILESTOINSTALL) \
	$(CMAFILES)
ifeq '$(HASNATDYNLINK)' 'true'
DO_NATDYNLINK = yes
FILESTOINSTALL += $(CMXSFILES) $(CMXAFILES) $(CMOFILESTOINSTALL:.cmo=.cmx)
else
DO_NATDYNLINK =
endif

ALLDFILES = $(addsuffix .d,$(ALLSRCFILES) $(VDFILE))

# Compilation targets #########################################################

all:
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" pre-all
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" real-all
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" post-all
.PHONY: all

all.timing.diff:
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" pre-all
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" real-all.timing.diff TIME_OF_PRETTY_BUILD_EXTRA_FILES=""
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" post-all
.PHONY: all.timing.diff

make-pretty-timed-before:: TIME_OF_BUILD_FILE=$(TIME_OF_BUILD_BEFORE_FILE)
make-pretty-timed-after:: TIME_OF_BUILD_FILE=$(TIME_OF_BUILD_AFTER_FILE)
make-pretty-timed make-pretty-timed-before make-pretty-timed-after::
	$(HIDE)rm -f pretty-timed-success.ok
	$(HIDE)($(MAKE) --no-print-directory -f "$(PARENT)" $(TGTS) TIMED=1 2>&1 && touch pretty-timed-success.ok) | tee -a $(TIME_OF_BUILD_FILE)
	$(HIDE)rm pretty-timed-success.ok # must not be -f; must fail if the touch failed
print-pretty-timed::
	$(HIDE)$(COQMAKE_ONE_TIME_FILE) $(TIME_OF_BUILD_FILE) $(TIME_OF_PRETTY_BUILD_FILE) $(TIME_OF_PRETTY_BUILD_EXTRA_FILES)
print-pretty-timed-diff::
	$(HIDE)$(COQMAKE_BOTH_TIME_FILES) --sort-by=$(TIMING_SORT_BY) $(TIME_OF_BUILD_BEFORE_FILE) $(TIME_OF_BUILD_AFTER_FILE) $(TIME_OF_PRETTY_BOTH_BUILD_FILE) $(TIME_OF_PRETTY_BUILD_EXTRA_FILES)
ifeq (,$(BEFORE))
print-pretty-single-time-diff::
	@echo 'Error: Usage: $(MAKE) print-pretty-single-time-diff BEFORE=path/to/file.v.before-timing AFTER=path/to/file.v.after-timing'
	$(HIDE)false
else
ifeq (,$(AFTER))
print-pretty-single-time-diff::
	@echo 'Error: Usage: $(MAKE) print-pretty-single-time-diff BEFORE=path/to/file.v.before-timing AFTER=path/to/file.v.after-timing'
	$(HIDE)false
else
print-pretty-single-time-diff::
	$(HIDE)$(COQMAKE_BOTH_SINGLE_TIMING_FILES) --sort-by=$(TIMING_SORT_BY) $(BEFORE) $(AFTER) $(TIME_OF_PRETTY_BUILD_FILE) $(TIME_OF_PRETTY_BUILD_EXTRA_FILES)
endif
endif
pretty-timed:
	$(HIDE)$(MAKE) --no-print-directory -f "$(PARENT)" make-pretty-timed
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" print-pretty-timed
.PHONY: pretty-timed make-pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed print-pretty-timed-diff print-pretty-single-time-diff

# Extension points for actions to be performed before/after the all target
pre-all::
	@# Extension point
	$(HIDE)if [ "$(COQMAKEFILE_VERSION)" != "$(COQ_VERSION)" ]; then\
	  echo "W: This Makefile was generated by Coq $(COQMAKEFILE_VERSION)";\
	  echo "W: while the current Coq version is $(COQ_VERSION)";\
	fi
.PHONY: pre-all

post-all::
	@# Extension point
.PHONY: post-all

real-all: $(VOFILES) $(if $(USEBYTE),bytefiles,optfiles)
.PHONY: real-all

real-all.timing.diff: $(VOFILES:.vo=.v.timing.diff)
.PHONE: real-all.timing.diff

bytefiles: $(CMOFILES) $(CMAFILES)
.PHONY: bytefiles

optfiles: $(if $(DO_NATDYNLINK),$(CMXSFILES))
.PHONY: optfiles

# FIXME, see Ralf's bugreport
quick: $(VOFILES:.vo=.vio)
.PHONY: quick

vio2vo:
	$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) \
		-schedule-vio2vo $(J) $(VOFILES:%.vo=%.vio)
.PHONY: vio2vo

quick2vo:
	$(HIDE)make -j $(J) quick
	$(HIDE)VIOFILES=$$(for vofile in $(VOFILES); do \
	  viofile="$$(echo "$$vofile" | sed "s/\.vo$$/.vio/")"; \
	  if [ "$$vofile" -ot "$$viofile" -o ! -e "$$vofile" ]; then printf "$$viofile "; fi; \
	done); \
	echo "VIO2VO: $$VIOFILES"; \
	if [ -n "$$VIOFILES" ]; then \
	  $(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio2vo $(J) $$VIOFILES; \
	fi
.PHONY: quick2vo

checkproofs:
	$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) \
		-schedule-vio-checking $(J) $(VOFILES:%.vo=%.vio)
.PHONY: checkproofs

validate: $(VOFILES)
	$(TIMER) $(COQCHK) $(COQCHKFLAGS) $^
.PHONY: validate

only: $(TGTS)
.PHONY: only

# Documentation targets #######################################################

html: $(GLOBFILES) $(VFILES)
	$(SHOW)'COQDOC -d html $(GAL)'
	$(HIDE)mkdir -p html
	$(HIDE)$(COQDOC) \
		-toc $(COQDOCFLAGS) -html $(GAL) $(COQDOCLIBS) -d html $(VFILES)

mlihtml: $(MLIFILES:.mli=.cmi)
	$(SHOW)'CAMLDOC -d $@'
	$(HIDE)mkdir $@ || rm -rf $@/*
	$(HIDE)$(CAMLDOC) -html \
		-d $@ -m A $(CAMLDEBUG) $(CAMLDOCFLAGS) $(MLIFILES)

all-mli.tex: $(MLIFILES:.mli=.cmi)
	$(SHOW)'CAMLDOC -latex $@'
	$(HIDE)$(CAMLDOC) -latex \
		-o $@ -m A $(CAMLDEBUG) $(CAMLDOCFLAGS) $(MLIFILES)

gallina: $(GFILES)

all.ps: $(VFILES)
	$(SHOW)'COQDOC -ps $(GAL)'
	$(HIDE)$(COQDOC) \
		-toc $(COQDOCFLAGS) -ps $(GAL) $(COQDOCLIBS) \
		-o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all.pdf: $(VFILES)
	$(SHOW)'COQDOC -pdf $(GAL)'
	$(HIDE)$(COQDOC) \
		-toc $(COQDOCFLAGS) -pdf $(GAL) $(COQDOCLIBS) \
		-o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

# FIXME: not quite right, since the output name is different
gallinahtml: GAL=-g
gallinahtml: html

all-gal.ps: GAL=-g
all-gal.ps: all.ps

all-gal.pdf: GAL=-g
all-gal.pdf: all.pdf

# ?
beautify: $(BEAUTYFILES)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'
.PHONY: beautify

# Installation targets ########################################################
#
# There rules can be extended in Makefile.local
# Extensions can't assume when they run.

install:
	$(HIDE)for f in $(FILESTOINSTALL); do\
	 df="`$(COQMKFILE) -destination-of "$$f" $(COQLIBS)`";\
	 if [ "$$?" != "0" -o -z "$$df" ]; then\
	   echo SKIP "$$f" since it has no logical path;\
	 else\
	   install -d "$(COQLIBINSTALL)/$$df" &&\
	   install -m 0644 "$$f" "$(COQLIBINSTALL)/$$df" &&\
	   echo INSTALL "$$f" "$(COQLIBINSTALL)/$$df";\
	 fi;\
	done
	$(HIDE)$(MAKE) install-extra -f "$(SELF)"
install-extra::
	@# Extension point
.PHONY: install install-extra

install-byte:
	$(HIDE)for f in $(BYTEFILESTOINSTALL); do\
	 df="`$(COQMKFILE) -destination-of "$$f" $(COQLIBS)`";\
	 if [ "$$?" != "0" -o -z "$$df" ]; then\
	   echo SKIP "$$f" since it has no logical path;\
	 else\
	   install -d "$(COQLIBINSTALL)/$$df" &&\
	   install -m 0644 "$$f" "$(COQLIBINSTALL)/$$df" &&\
	   echo INSTALL "$$f" "$(COQLIBINSTALL)/$$df";\
	 fi;\
	done

install-doc:: html mlihtml
	@# Extension point
	$(HIDE)install -d "$(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/html"
	$(HIDE)for i in html/*; do \
	 dest="$(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/$$i";\
	 install -m 0644 "$$i" "$$dest";\
	 echo INSTALL "$$i" "$$dest";\
	done
	$(HIDE)install -d \
		"$(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/mlihtml"
	$(HIDE)for i in mlihtml/*; do \
	 dest="$(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/$$i";\
	 install -m 0644 "$$i" "$$dest";\
	 echo INSTALL "$$i" "$$dest";\
	done
.PHONY: install-doc

uninstall::
	@# Extension point
	$(HIDE)for f in $(FILESTOINSTALL); do \
	 df="`$(COQMKFILE) -destination-of "$$f" $(COQLIBS)`" &&\
	 instf="$(COQLIBINSTALL)/$$df/`basename $$f`" &&\
	 rm -f "$$instf" &&\
	 echo RM "$$instf" &&\
	 (rmdir "$(call concat_path,,$(COQLIBINSTALL)/$$df/)" 2>/dev/null || true); \
	done
.PHONY: uninstall

uninstall-doc::
	@# Extension point
	$(SHOW)'RM $(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/html'
	$(HIDE)rm -rf "$(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/html"
	$(SHOW)'RM $(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/mlihtml'
	$(HIDE)rm -rf "$(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/mlihtml"
	$(HIDE) rmdir "$(COQDOCINSTALL)/$(INSTALLCOQDOCROOT)/" || true
.PHONY: uninstall-doc

# Cleaning ####################################################################
#
# There rules can be extended in Makefile.local
# Extensions can't assume when they run.

clean::
	@# Extension point
	$(SHOW)'CLEAN'
	$(HIDE)rm -f $(CMOFILES)
	$(HIDE)rm -f $(CMIFILES)
	$(HIDE)rm -f $(CMAFILES)
	$(HIDE)rm -f $(CMOFILES:.cmo=.cmx)
	$(HIDE)rm -f $(CMXAFILES)
	$(HIDE)rm -f $(CMXSFILES)
	$(HIDE)rm -f $(CMOFILES:.cmo=.o)
	$(HIDE)rm -f $(CMXAFILES:.cmxa=.a)
	$(HIDE)rm -f $(ALLDFILES)
	$(HIDE)rm -f $(NATIVEFILES)
	$(HIDE)find . -name .coq-native -type d -empty -delete
	$(HIDE)rm -f $(VOFILES)
	$(HIDE)rm -f $(VOFILES:.vo=.vio)
	$(HIDE)rm -f $(GFILES)
	$(HIDE)rm -f $(BEAUTYFILES) $(VFILES:=.old)
	$(HIDE)rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob all-mli.tex
	$(HIDE)rm -f $(VFILES:.v=.glob)
	$(HIDE)rm -f $(VFILES:.v=.tex)
	$(HIDE)rm -f $(VFILES:.v=.g.tex)
	$(HIDE)rm -f pretty-timed-success.ok
	$(HIDE)rm -rf html mlihtml
.PHONY: clean

cleanall:: clean
	@# Extension point
	$(SHOW)'CLEAN *.aux *.timing'
	$(HIDE)rm -f $(foreach f,$(VFILES:.v=),$(dir $(f)).$(notdir $(f)).aux)
	$(HIDE)rm -f $(TIME_OF_BUILD_FILE) $(TIME_OF_BUILD_BEFORE_FILE) $(TIME_OF_BUILD_AFTER_FILE) $(TIME_OF_PRETTY_BUILD_FILE) $(TIME_OF_PRETTY_BOTH_BUILD_FILE)
	$(HIDE)rm -f $(VOFILES:.vo=.v.timing)
	$(HIDE)rm -f $(VOFILES:.vo=.v.before-timing)
	$(HIDE)rm -f $(VOFILES:.vo=.v.after-timing)
	$(HIDE)rm -f $(VOFILES:.vo=.v.timing.diff)
.PHONY: cleanall

archclean::
	@# Extension point
	$(SHOW)'CLEAN *.cmx *.o'
	$(HIDE)rm -f $(NATIVEFILES)
	$(HIDE)rm -f $(CMOFILES:%.cmo=%.cmx)
.PHONY: archclean


# Compilation rules ###########################################################

$(MLIFILES:.mli=.cmi): %.cmi: %.mli
	$(SHOW)'CAMLC -c $<'
	$(HIDE)$(CAMLC) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) $<

$(ML4FILES:.ml4=.cmo): %.cmo: %.ml4
	$(SHOW)'CAMLC -pp -c $<'
	$(HIDE)$(CAMLC) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) $(PP) -impl $<

$(ML4FILES:.ml4=.cmx): %.cmx: %.ml4
	$(SHOW)'CAMLOPT -pp -c $(FOR_PACK) $<'
	$(HIDE)$(CAMLOPTC) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) $(PP) $(FOR_PACK) -impl $<

$(MLFILES:.ml=.cmo): %.cmo: %.ml
	$(SHOW)'CAMLC -c $<'
	$(HIDE)$(CAMLC) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) $<

$(MLFILES:.ml=.cmx): %.cmx: %.ml
	$(SHOW)'CAMLOPT -c $(FOR_PACK) $<'
	$(HIDE)$(CAMLOPTC) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) $(FOR_PACK) $<


$(MLLIBFILES:.mllib=.cmxs): %.cmxs: %.cmxa
	$(SHOW)'CAMLOPT -shared -o $@'
	$(HIDE)$(CAMLOPTLINK) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) \
		-linkall -shared -o $@ $<

$(MLLIBFILES:.mllib=.cma): %.cma: | %.mllib
	$(SHOW)'CAMLC -a -o $@'
	$(HIDE)$(CAMLLINK) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) -a -o $@ $^

$(MLLIBFILES:.mllib=.cmxa): %.cmxa: | %.mllib
	$(SHOW)'CAMLOPT -a -o $@'
	$(HIDE)$(CAMLOPTLINK) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) -a -o $@ $^


$(MLPACKFILES:.mlpack=.cmxs): %.cmxs: %.cmxa
	$(SHOW)'CAMLOPT -shared -o $@'
	$(HIDE)$(CAMLOPTLINK) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) \
		-shared -linkall -o $@ $<

$(MLPACKFILES:.mlpack=.cmxa): %.cmxa: %.cmx
	$(SHOW)'CAMLOPT -a -o $@'
	$(HIDE)$(CAMLOPTLINK) $(CAMLDEBUG) $(CAMLFLAGS) -a -o $@ $<

$(MLPACKFILES:.mlpack=.cma): %.cma: %.cmo | %.mlpack
	$(SHOW)'CAMLC -a -o $@'
	$(HIDE)$(CAMLLINK) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) -a -o $@ $^

$(MLPACKFILES:.mlpack=.cmo): %.cmo: | %.mlpack
	$(SHOW)'CAMLC -pack -o $@'
	$(HIDE)$(CAMLLINK) $(CAMLDEBUG) $(CAMLFLAGS) -pack -o $@ $^

$(MLPACKFILES:.mlpack=.cmx): %.cmx: | %.mlpack
	$(SHOW)'CAMLOPT -pack -o $@'
	$(HIDE)$(CAMLOPTLINK) $(CAMLDEBUG) $(CAMLFLAGS) -pack -o $@ $^

# This rule is for _CoqProject with no .mllib nor .mlpack
$(filter-out $(MLLIBFILES:.mllib=.cmxs) $(MLPACKFILES:.mlpack=.cmxs) $(addsuffix .cmxs,$(PACKEDFILES)) $(addsuffix .cmxs,$(LIBEDFILES)),$(MLFILES:.ml=.cmxs) $(ML4FILES:.ml4=.cmxs)): %.cmxs: %.cmx
	$(SHOW)'[deprecated,use-mllib-or-mlpack] CAMLOPT -shared -o $@'
	$(HIDE)$(CAMLOPTLINK) $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) \
		-shared -o $@ $<

ifneq (,$(TIMING))
TIMING_EXTRA = > $<.$(TIMING_EXT)
else
TIMING_EXTRA =
endif

$(VOFILES): %.vo: %.v
	$(SHOW)COQC $<
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(TIMING_ARG) $(COQFLAGS) $< $(TIMING_EXTRA)

# FIXME ?merge with .vo / .vio ?
$(GLOBFILES): %.glob: %.v
	$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $<

$(VFILES:.v=.vio): %.vio: %.v
	$(SHOW)COQC -quick $<
	$(HIDE)$(TIMER) $(COQC) -quick $(COQDEBUG) $(COQFLAGS) $<

$(addsuffix .timing.diff,$(VFILES)): %.timing.diff : %.before-timing %.after-timing
	$(SHOW)PYTHON TIMING-DIFF $<
	$(HIDE)$(MAKE) --no-print-directory -f "$(SELF)" print-pretty-single-time-diff BEFORE=$*.before-timing AFTER=$*.after-timing TIME_OF_PRETTY_BUILD_FILE="$@"

$(BEAUTYFILES): %.v.beautified: %.v
	$(SHOW)'BEAUTIFY $<'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $<

$(GFILES): %.g: %.v
	$(SHOW)'GALLINA $<'
	$(HIDE)$(GALLINA) $<

$(TEXFILES): %.tex: %.v
	$(SHOW)'COQDOC -latex $<'
	$(HIDE)$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

$(GTEXFILES): %.g.tex: %.v
	$(SHOW)'COQDOC -latex -g $<'
	$(HIDE)$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

$(HTMLFILES): %.html: %.v %.glob
	$(SHOW)'COQDOC -html $<'
	$(HIDE)$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

$(GHTMLFILES): %.g.html: %.v %.glob
	$(SHOW)'COQDOC -html -g $<'
	$(HIDE)$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

# Dependency files ############################################################

ifneq ($(filter-out archclean clean cleanall printenv make-pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed print-pretty-timed-diff print-pretty-single-time-diff,$(MAKECMDGOALS)),)
 -include $(ALLDFILES)
else
 ifeq ($(MAKECMDGOALS),)
  -include $(ALLDFILES)
 endif
endif

.SECONDARY: $(ALLDFILES)

redir_if_ok = > "$@" || ( RV=$$?; rm -f "$@"; exit $$RV )

$(addsuffix .d,$(MLIFILES)): %.mli.d: %.mli
	$(SHOW)'CAMLDEP $<'
	$(HIDE)$(CAMLDEP) $(OCAMLLIBS) "$<" $(redir_if_ok)

$(addsuffix .d,$(ML4FILES)): %.ml4.d: %.ml4
	$(SHOW)'CAMLDEP -pp $<'
	$(HIDE)$(CAMLDEP) $(OCAMLLIBS) $(PP) -impl "$<" $(redir_if_ok)

$(addsuffix .d,$(MLFILES)): %.ml.d: %.ml
	$(SHOW)'CAMLDEP $<'
	$(HIDE)$(CAMLDEP) $(OCAMLLIBS) "$<" $(redir_if_ok)

$(addsuffix .d,$(MLLIBFILES)): %.mllib.d: %.mllib
	$(SHOW)'COQDEP $<'
	$(HIDE)$(COQDEP) $(OCAMLLIBS) -c "$<" $(redir_if_ok)

$(addsuffix .d,$(MLPACKFILES)): %.mlpack.d: %.mlpack
	$(SHOW)'COQDEP $<'
	$(HIDE)$(COQDEP) $(OCAMLLIBS) -c "$<" $(redir_if_ok)

# If this makefile is created using a _CoqProject we have coqdep get
# options from it. This avoids argument length limits for pathological
# projects. Note that extra options might be on the command line.
VDFILE_FLAGS:=$(if Make,-f Make,) $(CMDLINE_COQLIBS) $(CMDLINE_VFILES)

$(VDFILE).d: $(VFILES)
	$(SHOW)'COQDEP VFILES'
	$(HIDE)$(COQDEP) -dyndep var $(VDFILE_FLAGS) $(redir_if_ok)

# Misc ########################################################################

byte:
	$(HIDE)$(MAKE) all "OPT:=-byte" -f "$(SELF)"
.PHONY: byte

opt:
	$(HIDE)$(MAKE) all "OPT:=-opt" -f "$(SELF)"
.PHONY:	opt

# This is deprecated.  To extend this makefile use
# extension points and Makefile.local
printenv::
	$(warning printenv is deprecated)
	$(warning write extensions in Makefile.local or include Makefile.conf)
	@echo 'LOCAL = $(LOCAL)'
	@echo 'COQLIB = $(COQLIB)'
	@echo 'DOCDIR = $(DOCDIR)'
	@echo 'OCAMLFIND = $(OCAMLFIND)'
	@echo 'CAMLP5O = $(CAMLP5O)'
	@echo 'CAMLP5BIN = $(CAMLP5BIN)'
	@echo 'CAMLP5LIB = $(CAMLP5LIB)'
	@echo 'CAMLP5OPTIONS = $(CAMLP5OPTIONS)'
	@echo 'HASNATDYNLINK = $(HASNATDYNLINK)'
	@echo 'SRC_SUBDIRS = $(SRC_SUBDIRS)'
	@echo 'COQ_SRC_SUBDIRS = $(COQ_SRC_SUBDIRS)'
	@echo 'OCAMLFIND = $(OCAMLFIND)'
	@echo 'PP = $(PP)'
	@echo 'COQFLAGS = $(COQFLAGS)'
	@echo 'COQLIBINSTALL = $(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL = $(COQDOCINSTALL)'
.PHONY:	printenv

# Generate a .merlin file.  If you need to append directives to this
# file you can extend the merlin-hook target in Makefile.local
.merlin:
	$(SHOW)'FILL .merlin'
	$(HIDE)echo 'FLG $(COQMF_CAMLFLAGS)' > .merlin
	$(HIDE)echo 'B $(COQLIB)' >> .merlin
	$(HIDE)echo 'S $(COQLIB)' >> .merlin
	$(HIDE)$(foreach d,$(COQ_SRC_SUBDIRS), \
		echo 'B $(COQLIB)$(d)' >> .merlin;)
	$(HIDE)$(foreach d,$(COQ_SRC_SUBDIRS), \
		echo 'S $(COQLIB)$(d)' >> .merlin;)
	$(HIDE)$(foreach d,$(SRC_SUBDIRS), echo 'B $(d)' >> .merlin;)
	$(HIDE)$(foreach d,$(SRC_SUBDIRS), echo 'S $(d)' >> .merlin;)
	$(HIDE)$(MAKE) merlin-hook -f "$(SELF)"
.PHONY: merlin

merlin-hook::
	@# Extension point
.PHONY: merlin-hook

# prints all variables
debug:
	$(foreach v,\
		$(sort $(filter-out $(INITIAL_VARS) INITIAL_VARS,\
	       		$(.VARIABLES))),\
	       	$(info $(v) = $($(v))))
.PHONY: debug

.DEFAULT_GOAL := all
