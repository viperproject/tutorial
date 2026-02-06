# Tutorial

This repo contains the sources of the official Viper tutorial (http://viper.ethz.ch/tutorial). 

Feel free to submit your fixes and additions via pull requests. 

Please report technical issues via the issue tracker.

## Building

The tutorial uses [`mdbook`](https://rust-lang.github.io/mdBook/) to generate HTML pages. To build, run (from the repository root):

```bash
mdbook build
```

This creates a folder called `book`. To watch for changes and automatically rebuild files when the source content updates:

```bash
mdbook serve
```

## Editing

### Interactive Viper code snippets

In order to create an interacative code snippet (which can be verified directly in the web browser), insert the code in the following way: 

````md
```viper,editable,playground
method foobar() 
{
	assert false
}
```
````

### Including exercises

Use the following syntax in order to include an exercise to the tutorial: 

```md
> **Exercise**
> * ...
```
