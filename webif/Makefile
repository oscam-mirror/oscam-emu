HOSTCC ?= gcc
HOSTCFLAGS ?= -O2 \
 -W -Wall -Wextra -Wno-sign-compare \
 -Wshadow -Wformat-security -Wstrict-prototypes

# Setup quiet build
Q =
SAY = @true
ifndef V
Q = @
NP = --no-print-directory
SAY = @echo
endif

# Check if WEBIF_WIKI is enabled
WEBIF_WIKI_ENABLED := $(shell ../config.sh --enabled WEBIF_WIKI 2>/dev/null)

ifeq ($(WEBIF_WIKI_ENABLED),Y)
all: pages.c pages_wiki.c
else
all: pages.c
endif

pages.c: pages_gen ../config.h
	$(SAY) "GEN	webif/$@"
	$(Q)./pages_mkdep
	$(Q)./pages_gen

-include pages.dep

pages_gen: Makefile pages_gen.c
	$(SAY) "HOSTCC	webif/$@"
	$(Q)$(HOSTCC) $(HOSTCFLAGS) ../minilzo/minilzo.c pages_gen.c -o $@

# Wiki help generation (only if WEBIF_WIKI is enabled and wiki submodule exists)
pages_wiki.c: wiki_gen ../config.h
	$(SAY) "GEN	webif/$@"
	$(Q)if [ -d "../wiki/pages/configuration" ]; then \
		./wiki_gen ../wiki/pages/configuration; \
	else \
		echo "WIKI	ERROR: wiki submodule not found!"; \
		echo "WIKI	Run: git submodule update --init"; \
		exit 1; \
	fi

wiki_gen: Makefile wiki_gen.c
	$(SAY) "HOSTCC	webif/$@"
	$(Q)$(HOSTCC) $(HOSTCFLAGS) ../minilzo/minilzo.c wiki_gen.c -o $@

clean:
	@-for FILE in pages_gen pages.dep pages.bin pages.bin.compressed pages.h pages.c wiki_gen pages_wiki.h pages_wiki.c is_defined.txt; do \
		if [ -f $$FILE ]; then echo "RM	webif/$$FILE"; fi; \
		rm -rf $$FILE; \
	done

distclean: clean
