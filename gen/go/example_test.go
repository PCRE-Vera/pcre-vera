// The README's Go example, kept here so that it is run rather than admired.

package pcretruste_test

import (
	"fmt"
	"log"

	pcretruste "github.com/jedisct1/pcre-truste/gen/go"
)

func Example() {
	re, err := pcretruste.Compile(`(?<user>\w+)@(?<host>[\w.]+)`, pcretruste.Options{})
	if err != nil {
		log.Fatal(err)
	}

	subject := []byte("write to alice@example.org, please")
	ovector, err := re.Match(subject, 0, 0, pcretruste.DefaultLimits())
	if err != nil {
		log.Fatal(err)
	}
	if ovector == nil {
		fmt.Println("no match")
		return
	}

	group := func(n int) string { return string(subject[ovector[2*n]:ovector[2*n+1]]) }
	fmt.Printf("%s is %s at %s\n",
		group(0), group(re.SubexpIndex("user")), group(re.SubexpIndex("host")))
	// Output:
	// alice@example.org is alice at example.org
}
