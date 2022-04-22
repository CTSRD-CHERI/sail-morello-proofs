T_CHERI_DIR = ../t-cheri
MORELLO_DIR = ../sail-morello
AFP_DIR = ../afp
PROOF_DIR = $(realpath .)
ISABELLE = isabelle

# Attempt to work with either sail from opam or built from repo in SAIL_DIR
ifneq ($(SAIL_DIR),)
# Use sail repo in SAIL_DIR
SAIL:=$(SAIL_DIR)/sail
export SAIL_DIR
else
# Use sail from opam package
SAIL_DIR:=$(shell opam config var sail:share)
SAIL:=sail
endif

# Same for Lem
ifneq ($(LEM_DIR),)
export LEM_DIR
else
LEM_DIR:=$(shell opam config var lem:share)
endif

# Check if the sail-morello directory has snapshots of the Lem and Sail Isabelle libraries
ifneq ($(wildcard $(MORELLO_DIR)/lib/isabelle),)
  SAIL_LEM_LIB = $(MORELLO_DIR)/lib/isabelle/lem
  SAIL_ISA_LIB = $(MORELLO_DIR)/lib/isabelle/sail
else
  SAIL_LEM_LIB = $(LEM_DIR)/isabelle-lib
  SAIL_ISA_LIB = $(SAIL_DIR)/lib/isabelle
endif

GEN_LEMMAS = $(T_CHERI_DIR)/tools/gen_lemmas
MORELLO_SAIL_DIR = $(MORELLO_DIR)/src
MORELLO_ISA_DIR = $(MORELLO_DIR)/isabelle
MORELLO_PATCHES_DIR = $(MORELLO_SAIL_DIR)/patches

ISA_DEPS = $(SAIL_LEM_LIB) $(SAIL_ISA_LIB) $(AFP_DIR)/thys/Word_Lib $(T_CHERI_DIR)/model/isabelle $(MORELLO_ISA_DIR)
ISA_DEP_FLAGS = $(foreach dir,$(ISA_DEPS),-d $(dir))
ISA_BUILD_FLAGS = -v $(ISA_DEP_FLAGS)

SMT_SAIL_BASE = prelude.sail builtins.sail v8_base.sail
SMT_SAIL_BASE_PATHS = $(addprefix $(MORELLO_SAIL_DIR)/,$(SMT_SAIL_BASE))

SAIL_FLAGS = -verbose 1 -memo_z3 -no_effects -non_lexical_flow -no_warn
SMT_FLAGS = # -mono_rewrites

EXTRA_GEN_FLAGS = -splice $(MORELLO_PATCHES_DIR)/translation_stubs.sail -splice $(MORELLO_PATCHES_DIR)/unknown_capability.sail -splice $(MORELLO_PATCHES_DIR)/write_tag.sail

isail: $(SMT_SAIL_BASE_PATHS) properties.sail
	$(SAIL) -i $(SAIL_FLAGS) $^

smt: $(SMT_SAIL_BASE_PATHS) properties.sail
	$(SAIL) -smt $(SAIL_FLAGS) $(SMT_FLAGS) $^

gen_lemmas: morello.json
	$(GEN_LEMMAS) -src_dir $(MORELLO_SAIL_DIR) $(EXTRA_GEN_FLAGS) morello.json

check_proof:
	$(ISABELLE) build $(ISA_BUILD_FLAGS) -D .
