package pcrevera

import (
	"errors"
	"slices"
	"strings"
	"testing"
)

func TestTheArtifactHashIsAHash(t *testing.T) {
	if len(ArtifactSHA256) != 64 {
		t.Fatalf("ArtifactSHA256 = %q, want 64 characters", ArtifactSHA256)
	}
	if strings.Trim(ArtifactSHA256, "0123456789abcdef") != "" {
		t.Fatalf("ArtifactSHA256 = %q, want lowercase hexadecimal", ArtifactSHA256)
	}
}

func TestCompileAndMatch(t *testing.T) {
	re := MustCompile(`(\w+)@(\w+)`, Options{})
	if re.NumSubexp() != 2 {
		t.Fatalf("NumSubexp = %d, want 2", re.NumSubexp())
	}
	ovector, err := re.Match([]byte("mail: alice@example"), 0, 0, DefaultLimits(), DefaultConfig)
	if err != nil {
		t.Fatal(err)
	}
	want := []int32{6, 19, 6, 11, 12, 19}
	if !slices.Equal(ovector, want) {
		t.Fatalf("ovector = %v, want %v", ovector, want)
	}
}

func TestNoMatchIsNeitherAResultNorAnError(t *testing.T) {
	re := MustCompile("abc", Options{})
	ovector, err := re.Match([]byte("xyz"), 0, 0, DefaultLimits(), DefaultConfig)
	if err != nil || ovector != nil {
		t.Fatalf("Match = %v, %v; want nil, nil", ovector, err)
	}
}

func TestAGroupThatDidNotParticipateIsMinusOne(t *testing.T) {
	re := MustCompile("(a)|(b)", Options{})
	ovector, err := re.Match([]byte("b"), 0, 0, DefaultLimits(), DefaultConfig)
	if err != nil {
		t.Fatal(err)
	}
	if len(ovector) != 6 || ovector[2] != -1 || ovector[3] != -1 {
		t.Fatalf("ovector = %v, want the first group unset", ovector)
	}
}

func TestNamedGroups(t *testing.T) {
	re := MustCompile(`(?<year>\d{4})-(?<month>\d{2})`, Options{})
	if got := re.SubexpIndex("month"); got != 2 {
		t.Fatalf("SubexpIndex(month) = %d, want 2", got)
	}
	if got := re.SubexpIndex("day"); got != -1 {
		t.Fatalf("SubexpIndex(day) = %d, want -1", got)
	}
	names := re.SubexpNames()
	if len(names) != 2 || names["year"] != 1 {
		t.Fatalf("SubexpNames = %v", names)
	}
	// The map is a copy, so writing to it cannot reach the pattern.
	names["year"] = 99
	if re.SubexpIndex("year") != 1 {
		t.Fatal("SubexpNames handed out the pattern's own map")
	}
}

func TestSyntaxErrorCarriesTheCodeAndOffset(t *testing.T) {
	_, err := Compile("a[b", Options{})
	var failure *Error
	if !errors.As(err, &failure) {
		t.Fatalf("Compile = %v, want an *Error", err)
	}
	if failure.Kind != Syntax || failure.Code != 106 || failure.Offset != 3 {
		t.Fatalf("error = %+v, want syntax 106 at offset 3", failure)
	}
}

func TestAnUnsupportedConstructIsNotAPcre2Code(t *testing.T) {
	_, err := Compile(`(?=a)`, Options{})
	var failure *Error
	if !errors.As(err, &failure) || failure.Kind != UnsupportedFeature {
		t.Fatalf("Compile = %v, want UnsupportedFeature", err)
	}
	if failure.Code < 1000 {
		t.Fatalf("code = %d, want one of ours rather than a pcre2 code", failure.Code)
	}
}

func TestUnknownOptionBitsAreRefused(t *testing.T) {
	if _, err := Compile("a", Options{Flags: 1 << 20}); err == nil {
		t.Fatal("an option bit nothing defines was accepted")
	}
	re := MustCompile("a", Options{})
	if _, err := re.Match([]byte("a"), 0, 1<<20, DefaultLimits(), DefaultConfig); err == nil {
		t.Fatal("a match option bit nothing defines was accepted")
	}
}

func TestAStartOffsetPastTheSubjectIsBadInput(t *testing.T) {
	re := MustCompile("a", Options{})
	_, err := re.Match([]byte("aaa"), 4, 0, DefaultLimits(), DefaultConfig)
	var failure *Error
	if !errors.As(err, &failure) || failure.Kind != BadInput {
		t.Fatalf("Match = %v, want BadInput", err)
	}
	if _, err := re.Match([]byte("aaa"), 3, 0, DefaultLimits(), DefaultConfig); err != nil {
		t.Fatalf("a start offset at the end of the subject is legal: %v", err)
	}
}

func TestALimitPastWhatAnyTargetCouldHonorIsBadInput(t *testing.T) {
	re := MustCompile("a", Options{})
	limits := DefaultLimits()
	limits.Memory = MaxMemoryLimit + 1
	var failure *Error
	if _, err := re.Match([]byte("a"), 0, 0, limits, DefaultConfig); !errors.As(err, &failure) ||
		failure.Kind != BadInput {
		t.Fatal("a memory limit past the allocation ceiling was accepted")
	}
}

func TestAMatchOverBudgetIsResourceExceeded(t *testing.T) {
	re := MustCompile("(a*)*b", Options{})
	limits := Limits{Cost: 32, Stack: MaxStackLimit, Memory: MaxMemoryLimit}
	_, err := re.Match([]byte(strings.Repeat("a", 40)), 0, 0, limits, DefaultConfig)
	var failure *Error
	if !errors.As(err, &failure) || failure.Kind != ResourceExceeded {
		t.Fatalf("Match = %v, want ResourceExceeded", err)
	}
}

func TestACompiledPatternSurvivesConcurrentUse(t *testing.T) {
	re := MustCompile(`(\d+)`, Options{})
	done := make(chan bool)
	for range 8 {
		go func() {
			for range 200 {
				ovector, err := re.Match([]byte("abc 1234"), 0, 0, DefaultLimits(), DefaultConfig)
				if err != nil || len(ovector) != 4 || ovector[0] != 4 {
					done <- false
					return
				}
			}
			done <- true
		}()
	}
	for range 8 {
		if !<-done {
			t.Fatal("a concurrent match disagreed with a serial one")
		}
	}
}

func TestTheLengthCeilingIsTheI32One(t *testing.T) {
	// Every offset the engine reports is an i32 byte offset, so a pattern or a
	// subject past this could not be described. Reaching the branch itself
	// wants a two-gigabyte input, which this test will not allocate; what it
	// pins is the number, and the JavaScript side reaches the branch with a
	// subject whose length is faked.
	if MaxLength != 1<<31-1 {
		t.Fatalf("MaxLength = %d, want %d", MaxLength, 1<<31-1)
	}
	if uint64(MaxLength) != MaxMemoryLimit {
		t.Fatal("the length ceiling and the allocation ceiling have drifted apart")
	}
}

func TestAMatchConfigurationBesidesTheDefaultIsBadInput(t *testing.T) {
	// Memoized exists and is BadInput until M9 activates it; an ordinal
	// nobody defined is BadInput forever. The refusal is the generated
	// code's, so it is the same one in every language.
	re := MustCompile("abc", Options{})
	var failure *Error
	for _, config := range []MatchConfig{Memoized, 2, 0xFFFFFFFF, 1 << 32} {
		if _, err := re.Match([]byte("abc"), 0, 0, DefaultLimits(), config); !errors.As(err, &failure) ||
			failure.Kind != BadInput {
			t.Fatalf("config %d: want BadInput, got %v", config, err)
		}
		if _, err := re.WorstCaseCost(10, config); !errors.As(err, &failure) ||
			failure.Kind != BadInput {
			t.Fatalf("config %d: want BadInput from the accessor, got %v", config, err)
		}
	}
}

func TestTheAccessorsAnswerBeforeAnyMatchRuns(t *testing.T) {
	// A star runs on the Pike VM now, and the class describes the path that
	// will actually run: linear. The backtracking-bound shapes are pinned by
	// the corpus; what this checks is the wrapper plumbing.
	re := MustCompile("a*", Options{})
	class, err := re.ComplexityClass()
	if err != nil || class != Linear {
		t.Fatalf("ComplexityClass = %v, %v; want Linear", class, err)
	}
	cost, err := re.WorstCaseCost(10, DefaultConfig)
	if err != nil || cost == 0 {
		t.Fatalf("WorstCaseCost = %d, %v; want a positive bound", cost, err)
	}
	stack, err := re.WorstCaseStackEntries(10, DefaultConfig)
	if err != nil {
		t.Fatalf("WorstCaseStackEntries: %v", err)
	}
	mem, err := re.WorstCaseMemory(10, DefaultConfig)
	if err != nil || mem == 0 {
		t.Fatalf("WorstCaseMemory = %d, %v; want a positive bound", mem, err)
	}
	// The types line up with Limits by design, so the bounds pass unchanged.
	limits := Limits{Cost: cost, Stack: stack, Memory: mem}
	if _, err := re.Match([]byte("aaaaaaaaaa"), 0, 0, limits, DefaultConfig); err != nil {
		t.Fatalf("a match at the reported bounds failed: %v", err)
	}
}

func TestAPatternWithNoCertificateIsExceedsBudget(t *testing.T) {
	re := MustCompile("(?:a*)*", Options{})
	var failure *Error
	if _, err := re.ComplexityClass(); !errors.As(err, &failure) ||
		failure.Kind != ExceedsBudget {
		t.Fatalf("ComplexityClass: want ExceedsBudget, got %v", err)
	}
	if _, err := re.WorstCaseCost(10, DefaultConfig); !errors.As(err, &failure) ||
		failure.Kind != ExceedsBudget {
		t.Fatalf("WorstCaseCost: want ExceedsBudget, got %v", err)
	}
}

func TestALengthNoCounterHoldsIsBadInput(t *testing.T) {
	// The corpus pins every length all three languages can spell; a negative
	// int and a value past the counter's saturation point are the two only Go
	// can, so they are pinned here.
	re := MustCompile("abc", Options{})
	var failure *Error
	for _, n := range []int{-1, 1 << 53} {
		if _, err := re.WorstCaseCost(n, DefaultConfig); !errors.As(err, &failure) ||
			failure.Kind != BadInput {
			t.Fatalf("length %d: want BadInput, got %v", n, err)
		}
	}
}
