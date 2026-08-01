package pcretruste

import (
	"strings"
	"testing"
)

func TestArtifactHashAndGeneratedAgree(t *testing.T) {
	if Generated() != (ArtifactSHA256 != "") {
		t.Fatalf("Generated() = %v but ArtifactSHA256 = %q", Generated(), ArtifactSHA256)
	}
	if ArtifactSHA256 == "" {
		return
	}
	if len(ArtifactSHA256) != 64 {
		t.Fatalf("ArtifactSHA256 = %q, want 64 characters", ArtifactSHA256)
	}
	if strings.Trim(ArtifactSHA256, "0123456789abcdef") != "" {
		t.Fatalf("ArtifactSHA256 = %q, want lowercase hexadecimal", ArtifactSHA256)
	}
}
