# Tutorial

This repo contains the sources of the official Viper tutorial (http://viper.ethz.ch/tutorial). 

Feel free to submit your fixes and additions via pull requests. 

Please report technical issues via the issue tracker.

# Editing 

## Interactive Viper code snippets

In order to create an interacative code snippet (which can be verified directly in the web browser), inser the code in the following way: 


````Markdown

```silver {.runnable }
method foobar() 
{
	assert false
}
```
````

## Including exercises

Use the following syntax in order to include an exercise to the tutorial: 

```Markdown

//exercise//

* Sub-task A
* Sub-task B
* Sub-task C

///
```