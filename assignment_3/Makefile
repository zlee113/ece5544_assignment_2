CXX          = clang++
CXXFLAGS     = -rdynamic $(shell llvm-config --cxxflags) -fPIC -g -std=c++20
LDFLAGS      = $(shell llvm-config --ldflags | tr '\n' ' ') -Wl,--exclude-libs,ALL
BUILDDIR     = build
DEPDIR       = $(BUILDDIR)/.deps
DEPFLAGS     = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d

OPTIMIZER_SOURCES = unifiedpass.cpp
OPTIMIZER_LIBS    = $(OPTIMIZER_SOURCES:%.cpp=$(BUILDDIR)/%.so)

# finds all *-dom.bc files in tests/
DOM_TESTS    = $(wildcard tests/*-dom.bc)
DOM_OUTS     = $(DOM_TESTS:tests/%.bc=$(BUILDDIR)/tests/%-opt.ll)

# finds all *-licm.bc files in tests/
LICM_TESTS    = $(wildcard tests/*-licm.bc)
LICM_OUTS     = $(LICM_TESTS:tests/%.bc=$(BUILDDIR)/tests/%-opt.ll)

DEPFILES     = $(OPTIMIZER_SOURCES:%.cpp=$(DEPDIR)/%.d)

.PHONY: all clean tests
.SECONDARY:

all: $(OPTIMIZER_LIBS)

tests: $(DOM_OUTS)  | $(LICM_OUTS)

clean:
	rm -rf $(BUILDDIR)

$(BUILDDIR)/%.o: %.cpp $(DEPDIR)/%.d | $(DEPDIR) $(BUILDDIR)
	$(CXX) $(DEPFLAGS) $(CXXFLAGS) -c $< -o $@

$(BUILDDIR)/%.so: $(BUILDDIR)/%.o
	$(CXX) -shared $^ -o $@ $(LDFLAGS)
	
$(BUILDDIR)/tests/%-dom-opt.ll: tests/%-dom.bc $(OPTIMIZER_LIBS) | $(BUILDDIR)/tests
	opt -bugpoint-enable-legacy-pm=1 $(OPTIMIZER_LIBS:%=-load-pass-plugin=%) -passes='dominators' $< -o $@

$(BUILDDIR)/tests/%-dom-opt.ll: tests/%-licm.bc $(OPTIMIZER_LIBS) | $(BUILDDIR)/tests
	opt -bugpoint-enable-legacy-pm=1 $(OPTIMIZER_LIBS:%=-load-pass-plugin=%) -passes='licm' $< -o $@

$(BUILDDIR)/tests/%-opt.ll: $(BUILDDIR)/tests/%-opt.bc
	llvm-dis $< -o $@

$(DEPDIR) $(BUILDDIR) $(BUILDDIR)/tests:
	@mkdir -p $@

$(DEPFILES):
-include $(wildcard $(DEPFILES))