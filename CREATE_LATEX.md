# HowTo create a LateX documentation

For reference see also the [Isabelle tutorial](http://www21.in.tum.de/~nipkow/LNCS2283/).

## Preparations

Document creation requires `isabelle` as a command line tool. Make sure you have `isabelle` in your `$PATH` or set an `alias`.

Make sure you ahve a suitable `texlive` environment installed. Otherwise, LateX builds will fail.

## Quick build

Run the build command with:
```
isabelle build -D Isabelle
```

# Detailed instructions

## Sessions and build

A session manages all the documents that go into an output. Initiate the session with:


```
isabelle mkroot Isabelle
```

Next, run the build command with:
```
isabelle build -D Isabelle
```

## Notes

If you have a failure of builds due to using the `sorry` keyword in Isabelle, use:

```
isabelle build -o quick_and_dirty -D Isabelle
```

