CXX          = clang++
CXXFLAGS     = -rdynamic $(shell llvm-config --cxxflags) -fPIC -g -std=c++20
LDFLAGS      = $(shell llvm-config --ldflags | tr '\n' ' ') -Wl,--exclude-libs,ALL
BUILDDIR     = build
DEPDIR       = $(BUILDDIR)/.deps
DEPFLAGS     = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d

OPTIMIZER_SOURCES = unifiedpass.cpp
OPTIMIZER_LIBS    = $(OPTIMIZER_SOURCES:%.cpp=$(BUILDDIR)/%.so)

DOM_TESTS    = $(wildcard tests/*-dom.bc)
DOM_OUTS     = $(DOM_TESTS:tests/%.bc=$(BUILDDIR)/tests/%-opt.ll)

DCE_TESTS    = $(wildcard tests/*-dce.bc)
DCE_OUTS     = $(DCE_TESTS:tests/%.bc=$(BUILDDIR)/tests/%-opt.ll)

loop_invariant_code_motion_TESTS    = $(wildcard tests/*-loop_invariant_code_motion.bc)
loop_invariant_code_motion_OUTS     = $(loop_invariant_code_motion_TESTS:tests/%.bc=$(BUILDDIR)/tests/%-opt.ll)

DEPFILES     = $(OPTIMIZER_SOURCES:%.cpp=$(DEPDIR)/%.d)

.PHONY: all clean tests
.SECONDARY:

all: $(OPTIMIZER_LIBS)

tests: $(DOM_OUTS) $(DCE_OUTS) $(loop_invariant_code_motion_OUTS)

clean:
	rm -rf $(BUILDDIR)

$(BUILDDIR)/%.o: %.cpp $(DEPDIR)/%.d | $(DEPDIR) $(BUILDDIR)
	$(CXX) $(DEPFLAGS) $(CXXFLAGS) -c $< -o $@

$(BUILDDIR)/%.so: $(BUILDDIR)/%.o
	$(CXX) -shared $^ -o $@ $(LDFLAGS)
	
$(BUILDDIR)/tests/%-dom-opt.ll: tests/%-dom.bc $(OPTIMIZER_LIBS) | $(BUILDDIR)/tests
	opt -bugpoint-enable-legacy-pm=1 $(OPTIMIZER_LIBS:%=-load-pass-plugin=%) -passes='dominators' $< -o $@

$(BUILDDIR)/tests/%-dce-opt.ll: tests/%-dce.bc $(OPTIMIZER_LIBS) | $(BUILDDIR)/tests
	opt -bugpoint-enable-legacy-pm=1 $(OPTIMIZER_LIBS:%=-load-pass-plugin=%) -passes='dead-code-elimination' $< -o $@

$(BUILDDIR)/tests/%-loop_invariant_code_motion-opt.ll: tests/%-loop_invariant_code_motion.bc $(OPTIMIZER_LIBS) | $(BUILDDIR)/tests
	opt -bugpoint-enable-legacy-pm=1 $(OPTIMIZER_LIBS:%=-load-pass-plugin=%) -passes='loop_invariant_code_motion' $< -o $@

$(BUILDDIR)/tests/%-opt.ll: $(BUILDDIR)/tests/%-opt.bc
	llvm-dis $< -o $@

$(DEPDIR) $(BUILDDIR) $(BUILDDIR)/tests:
	@mkdir -p $@

$(DEPFILES):
-include $(wildcard $(DEPFILES))