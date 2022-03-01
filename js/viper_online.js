$(document).ready(initialize);
/**
 * Viper Online User Interface
 * @author Mathias Birrer, ETH Zürich
 */

// ======== Configuration ===========

/** The tool that is used, gets set in the HTML on tool load */
var tool = "";

/**The language of the tool used, gets set in the HTML on tool load */
var language = "";

/** Display tool options in the sidebar */
var showOptions = true;

/** Display tool examples in the sidebar */
var showExamples = false;

/** load a random exampe on startup */
var loadRandomExample = false;

/** Set a fixed height for the result bar.
 * Recommended on pages with a single editor.
 * Height is set to auto if empty string
 */
var resultBarFixedHeight = "300px";

/** Initial SideBar ("exmaples", "settings", "" = closed) */
var initialSideBar = "";

/** Enable logged sessions, through permalinks */
var enableLoggedSessions = false;

/** Show permalinks, only for pages with a single editor */
var enablePermalinks = false;

/** Max number of Lines of the editor */
var maxLines = 25;

/** Min number of Lines of the editor */
var minLines = 25;

/** Editor font settings
 * Font needs to be a monospaced font, unexpected behaviour otherwise
 */
var fontFamily = "Lucida Console, monospace";
var fontSize = "12pt";

/** Url of the Tool server, gets set in the HTML File on tool load */
var serverUrl = "";
var assetsUrl = "";

/** Support for multiple editors on same page (false = only one editor) */
var enableMultipleEditors = true;

/** The width (in % of the whole code editor) of the sidebar on large screens */
var widthSidebarNormal = 40;

/** The width (in % of the whole code editor) of the sidebar on narrow screens */
var widthSidebarNarrow = 70;

/** ======== Variables =========== */

/** Display log messages in the console */
var logging = false;

/** used to measure runtime */
var run_start = 0;

/** The session key if page opened through permalink */
var loggedSessionKey = null;

/** List of examples per editor */
var examples = {};
/** List of available options per editor */
var options = {};

/** List of available backends per editor */
var backends = {};

/** Saves the currently active backend for each editor */
var activeBackend = {};

/** True if sideBar is visible */
var sidebarOpen = {}


/** Defines client error messages */
var errors = new function() {
	this.error600 = {
		title : "600 - Unknown Error",
		message : "An unknown error occured. This is most likely due to a failure on the server. Please try again later. If the problem perists please inform the server administrator.."
	}
    this.error601 = {
		title : "601 - Failed To Start Session",
		message : "An unknown error occured while trying to start a new session with the server."
	}
	this.error602 = {
		title : "602 - Failed To Get Status",
		message : "An unknown error occured while trying to get the status of the current session."
	}
	this.error603 = {
		title : "603 - Failed To Get Result",
		message : "An unknown error occured while trying to get a result from the server."
	}	
	this.error604 = {
		title : "604 - Failed To Load Session",
		message : "An unknown error occured while trying to load the session."
	}
	this.error605 = {
		title : "605 - Failed To Load Session Result",
		message : "An unknown error occured while trying to get a result for the restored session."
	}
}

/** The object to store all open editors with their editor numbers */
var editors = {}; 



/** The object to store running status of editors */
var running = {};

/** The object to store editor options */
var options = {};

/** The object to store editor numbers associated with open sessionkeys */
var editorNrBySessionKey = {};

/** The object to store open session keys associated with editor numbers */
var sessionKeyByEditorNr = {};

/** The object to store numbers of errors per editor in the previous verification */
var errors = {};

/* ========= Getters / Setters =========== */


/**
 * Add a new editor to the 'editors' object.
 * @param editorNr {Integer} The editor number
 * @param editor The Ace editor object
 */
function addEditor(editorNr, editor){
	editors[editorNr] = editor;
}

/**
 * Get the Ace editor object with the editor number
 * @param editorNr {Integer} The editor number
 * @returns The Ace editor object
 */
function getEditor(editorNr){
	if(editorNr in editors){
		return editors[editorNr];
	} else return null;
}

/**
 * Add a new session with the sessionkey and editor number
 * @param editorNr The editor number
 * @param sessionKey The session key
 */
function addSession(editorNr, sessionKey){
	editorNrBySessionKey[sessionKey] = editorNr;
	sessionKeyByEditorNr[editorNr] = sessionKey;
}

/**
 * Get the editor number associated with a session key
 * @param sessionKey The session key
 * @returns The editor number
 */
function getEditorNrBySession(sessionKey){
	if(sessionKey in editorNrBySessionKey){
		return editorNrBySessionKey[sessionKey];
	} else return null;
}

/**
 * Get the session key associated with a editor number
 * @param editorNr The editor number
 * @returns The session key
 */
function getSessionKeyByEditorNr(editorNr){
	if(editorNr in sessionKeyByEditorNr){
		return sessionKeyByEditorNr[editorNr];
	} else return null;
}


/* ============= Initialization ============ */

/**
 * Preliminary steps before initialization of the editors.
 */
function initialize() {

	// Make links open new tabs
	$('a[rel="external"][href]').click(function() {
		window.open($(this).attr("href"), null, "").focus();
		return false;
	});

	// Load language file from tool server
	$("head").append("<script type='text/javascript' src='" + serverUrl + "comm/" + tool + "/language" + "'></script>");
	
	//Make the tool ready!
	wakeupTool();

	// Build editors
	initializeEditors();
	
}

/**
 * Find all editors on page and initialize them.
 */
function initializeEditors(){
	var editorWrapper = $(".editor");
	
	if(editorWrapper.length > 0){
		var editorNr = 100;
		$.each(editorWrapper, function(key, editor){
			editorSetup(editor, editorNr);
			editorNr = editorNr + 1;
		})
	} else {
		log("The editor setup failed because there is no element with class 'editor' defined!");
	}
}

/**
 * Prepares a single editor.
 * - Initialization of Ace
 * - Add editor to internal data structure
 * - Prepare layout
 * - Initialize sidebar
 * - Register clicks
 * @param editorWrapper The div-element that wraps the editor
 * @param editorNr The editor number
 */
function editorSetup(editorWrapper, editorNr){
	var editorId = "editor-" + editorNr;
	if(editorWrapper != null) {
		//$.each(editor)
		$(editorWrapper).children().first().attr("id", editorId);
	    var editor = ace.edit(editorId);
	    editor.setTheme("ace/theme/textmate");
	    editor.getSession().setMode("ace/mode/" + language);
	    editor.setOptions({
	      maxLines: maxLines,
	      minLines: minLines,
	      fontFamily: fontFamily,
	      fontSize: fontSize
	    });
	    editor.setShowPrintMargin(false);
	    editor.getSession().setUseWorker(false);

	    /* Save editor */
	    addEditor(editorNr, editor);
	    
	  //wrap in editorContainer
	    $("#" + editorId).parent().wrapInner("<div id='container-" +  editorNr +"' class='editorContainer'></div>" );
	    
	    /* Build / Initialize the graphical part of the UI */
	    buildGUI(editorNr);
	    
	} else {
		log("The editor setup failed because editorWrapper was null!");
	}
}

/**
 * Builds the graphical user interface.
 * Important for integrity with the tutorial.
 * @param editorNr The editor number.
 */
function buildGUI (editorNr){
	
    /* add bottomBar */
    $("#container-" + editorNr ).append("<div id='bottomBar-" + editorNr + "' class='editorBottomBar'>"
    	+ "<img src='" + assetsUrl + "images/play.png' id='runButton-" + editorNr + "' class='runButton' />"
    	+ "<img src='" + assetsUrl + "images/load.gif' id='loadButton-" + editorNr + "' class='runButton' style='display: none;' />"
    	+ "<div id='bottomBarText-" + editorNr + "' class='bottomBarText' ></div>"
    	+ "<div class='optionsButtonWrapper'>"
    	+ (enablePermalinks?"<img src='" + assetsUrl + "images/pin.png' id='pinButton-" + editorNr + "' class='pinButton' rel='tooltip' title='Click here to get a permalink to this result!' onClick='displayPermalink(" + editorNr +")' />":"")
    	+ "<img src='" + assetsUrl + "images/options.png' id='optionsButton-" + editorNr + "' class='optionsButton' onClick='toggleSidebar(" + editorNr + ")' />"
    	+ "</div></div>");

    /* Hide Permalink */
    $("#pinButton-"+editorNr).hide();

    /* add sideBar */
    $("#container-" + editorNr ).prepend("<div id='sideBar-" + editorNr + "' class='editorSideBar' style='display: none;' ></div>");

    /* add resultBar */
    $("#container-" + editorNr ).after("<div id='resultBar-" + editorNr + "' class='editorResultBar' style='display: none;"
    						+ (resultBarFixedHeight == "" ? "" : "height: " + resultBarFixedHeight + "; overflow-y: scroll;")
    						+ "'><ul class='nav nav-tabs'></ul><div class=\"tab-content\"></div></div>");

    /* Load Sidebar content */
    initSidebar(editorNr);

    /* add event for run Button */
    $("#runButton-"+editorNr).click(function(event){
    	var elem = $(this);
    	runTool(elem.attr('id').substr(-3));
    });
    
    /* register tooltips */
    $('[rel="tooltip"]').tooltip();
}


/**
 * Initializes the sidebar of the specified editor, i.e. adds examples (and shows one in the editor) and options.
 * Also automatically restores a logged session (through a permalink) if requested.
 * @param editorNr The editor number
 */
function initSidebar(editorNr) {
	$sidebar = $("#sideBar-" + editorNr);

	// Add Sidebar menu (Settings/Examples) if both are enabled
	if(showOptions && showExamples) {
		$sidebar.append("<div class='sideBarMenu'>"
							+ "<div class='sideBarMenuIcon'><img class='settingsIcon' src='" + assetsUrl + "images/settings.png' /></div>"
							+ "<div class='sideBarMenuIcon'><img class='examplesIcon' src='" + assetsUrl + "images/examples.png' /></div>"
							+ "</div>");
		$("#sideBar-" + editorNr + " .sideBarMenu .settingsIcon").parent().click(function(){
			changeSideBar(editorNr, "settings");
		});
		$("#sideBar-" + editorNr + " .sideBarMenu .examplesIcon").parent().click(function(){
			changeSideBar(editorNr, "examples");
		});
	}

	
	//Add sideBar sections
	$("#sideBar-"+editorNr).append("<div id='backendSelect-"+editorNr+"' class='backendSelect'><p>Backend:</p><select></select></div>");
	
	if(showOptions) $sidebar.append("<div class='sideBarSettings'></div>");
	if(showExamples) $sidebar.append("<div class='sideBarExamples'></div>");

	
	$sidebarSettings = $("#sideBar-" + editorNr + " .sideBarSettings").html("- no options available -").hide();
	$sidebarExamples = $("#sideBar-" + editorNr + " .sideBarExamples").html("- no examples available -").hide();
	
	// Fetch Backends from server
	$.ajax({url: serverUrl + "comm/" + tool + "/backends",
		type: "GET",
		dataType: "json",
		crossDomain: true,
		success: function(backendJsonList) {
			var backendList = backendJsonList;
			var firstBackend = backendList[0]['backend_tag'];
			$.each(backendList, function(key, val){
				backends[val['backend_tag']] = val;
				$("#backendSelect-"+editorNr+" select").append("<option value='"+val['backend_tag']+"'>"+val['name']+"</option>");
				
			});
			
			$("#backendSelect-"+editorNr).change(function(){
				var backend = $("#backendSelect-"+editorNr+" option:selected").attr("value");
				changeBackend(editorNr, backend, false);
			});
			
			

			changeBackend(editorNr, firstBackend, true);
			
			// Show Examples if available
			changeSideBar(editorNr, (showExamples?"examples":"settings"));
		}
	});
	
	
	
	
	// Set sideBar initial state
	sidebarOpen[editorNr] = false;
	switch(initialSideBar){
	case "examples":
		changeSideBar(editorNr, "examples");
		toggleSidebar(editorNr);
		break;
	case "settings":
		changeSideBar(editorNr, "settings");
		toggleSidebar(editorNr);
		break;
	default:
		
	}
	
	// Load a logged session if session key is set
	if(enableLoggedSessions){
		loadLoggedSession(editorNr);
	}
	
	
}


/**
 * Perform an HTTP request to wake up the tool.
 */
function wakeupTool(){
	log(serverUrl + "comm/"+ tool + "/wakeup")
	$.ajax({url: serverUrl + "comm/" + tool + "/wakeup",
		type: "GET",
		crossDomain: true,
		success: function() {
			log("Wakeup performed!");
		},
		error: function() {
			log("Wakeup not successful!");
		}
	});
}

/* ============= User Interface Modifications ============= */



/**
 * Hides or shoes the sidebar of the editor with the specified number
 * @param editorNr The editorNr
 */
function toggleSidebar(editorNr) {
	$sidebar = $( "#sideBar-" + editorNr);
    $editor = $("#editor-" + editorNr);
    var editorWidth = $("#container-" + editorNr).width();
    var sidebarWidth = (editorWidth <= 400 ? widthSidebarNarrow : widthSidebarNormal);
    
    if(!sidebarOpen[editorNr]){
    	$editor.animate({
	    	width : (100 - sidebarWidth) + "%"
	    }, {duration : 200, queue : false, complete : function(){
	    	editor.resize();
	    }});
	    $sidebar.animate({
	    	width : sidebarWidth + "%"
	    }, {duration : 200, queue : false });
	    sidebarOpen[editorNr] = true;
    } else {
	    $editor.animate({
	    	width : "100%"
	    }, {duration : 200, queue : false, complete : function(){
	    	editor.resize();
	    }});
	    $sidebar.animate({
	    	width : "0px"
	    }, {duration : 200, queue : false});
	    sidebarOpen[editorNr] = false;
	}
	    var editor = getEditor(editorNr);
	    
	    $sidebar.toggle();
}


/**
 * Opens the result bar of the specified editor
 * @param editorNr The editor number
 */
function openResultBar(editorNr){
	$("#resultBar-" + editorNr).show("slow");
}

/**
 * Closes the result bar of the specified editor
 * @param editorNr The editor number
 */
function closeResultBar(editorNr){
	$("#resultBar-" + editorNr).hide("slow");
}


/**
 * Changes the backend, based on the user selection
 * @param editorNr The editor number
 * @param backendTag The unique identifier of the backend
 * @param init {Boolean} true if it's called by the sidebar initialization function
 */
function changeBackend(editorNr, backendTag, init){
	var backend = backends[backendTag];
	var sessionKey = getSessionKeyByEditorNr(editorNr);
	activeBackend[editorNr] = backendTag;
	
	if(showExamples){
		// Examples
		var exampleJsonList = backend['examples'];
		var items = [];
		examples[editorNr] = [];
		$sidebarExamples = $("#sideBar-" + editorNr + " .sideBarExamples");
		$.each(exampleJsonList, function(key, val) {
			items.push("<li id='example"+key+"'>"+escapeHTML(val.name)+"</li>");
			examples[editorNr].push(val.content);
		});

		if (items.length > 0) {
			var editor = getEditor(editorNr);
			$sidebarExamples.empty();
			var list = $("<ul/>", {'class': 'exampleList', html: items.join('')});
			list.appendTo($sidebarExamples);
			list.children().click(function() {
				editor.getSession().setValue(examples[editorNr][$(this).attr("id").substr(7)]);
			});

			if (sessionKey == null && init && loadRandomExample) { // Load a random example if no session is being loaded
				editor.getSession().setValue(examples[editorNr][Math.floor(Math.random()*examples[editorNr].length)]);
			}
		}

	}
	
	if(showOptions){
		var optionJsonList = backend['options'];
		var items = [];
		options[editorNr] = [];
		$sidebarSettings = $("#sideBar-" + editorNr + " .sideBarSettings");
		$.each(optionJsonList, function(key, val) {
			var optionId = "option_"+escapeHTML(val.tag)+"-"+editorNr;
			options[editorNr].push(optionId);
			
			items.push("<div class='settingsLeft'>"+escapeHTML(val.name)+":</div><div class='settingsRight'>");
			switch(val.option_type) {
				case "string":
				items.push("<input"+(val.default_value == undefined ? "" : " value=\""+escapeHTML(val.default_value)+"\"")+" id=\""+optionId+"\" type=\"text\">");
				break;
				case "integer":
				items.push("<input class=\"integer_option\" "+(val.default_value == undefined ? "0" : " value=\""+escapeHTML(val.default_value)+"\"")+" id=\""+optionId+"\">");
				break;
				case "boolean":
				items.push("<div class='slideThree'><input type=\"checkbox\""+((val.default_value != undefined && val.default_value == "true") ? " checked" : "")+" value=\"None\" id=\""+optionId+"\"><label for='slideThree'></label></div>");
				break;
				case "list":
				items.push("<select id=\""+optionId+"\">");
				$.each(val.values, function (k, v) {
					items.push("<option value=\""+k+"\""+((val.default_value == k || (k == 0 && val.default_value == undefined)) ? " selected" : "")+">"+escapeHTML(v)+"</option>");
				});
				items.push("</select>");
				break;
				default:
				items.push("<i>unknown option type</i>");
			}
			items.push("</div>");
		});
		
		if (items.length == 0) {
			$sidebarSettings.text("- no options available -");
		} else {
			$sidebarSettings.empty();
			$sidebarSettings.append($("<div/>", {'id': 'list_of_options-'+editorNr, html: items.join('')}));
			$(".integer_option").numeric(false);
		}
	}
}

/**
 * Toggles the sidebar between examlpes and options
 * @param editorNr The editor number
 * @param state Either "examples or "options"
 */
function changeSideBar(editorNr, state){
	if(state == "examples"){
		$("#sideBar-" + editorNr + " .sideBarSettings").hide();
		$("#sideBar-" + editorNr + " .sideBarExamples").show();
		$("#sideBar-" + editorNr + " .sideBarMenu .settingsIcon").parent().removeClass("active");
		$("#sideBar-" + editorNr + " .sideBarMenu .examplesIcon").parent().addClass("active");

	} else {
		$("#sideBar-" + editorNr + " .sideBarExamples").hide();
		$("#sideBar-" + editorNr + " .sideBarSettings").show();
		$("#sideBar-" + editorNr + " .sideBarMenu .settingsIcon").parent().addClass("active");
		$("#sideBar-" + editorNr + " .sideBarMenu .examplesIcon").parent().removeClass("active");
	}
}


/**
 * Changes the Editor with editorNr to the initial mode
 * @param editorNr The editor number
 */
function changeToInitialMode(editorNr){
	//remove event handler from editor
	$("#editor-"+editorNr).off("click");
	$("#runButton-"+editorNr).off("click");
	
	// change Icon & initialize run button
	var icon = $("#runButton-" + editorNr);
	changeIcon(editorNr, 'play.png');
	icon.click(function(){
    	runTool(editorNr);
	});
}

/**
 * Changes the Editor with editorNr to running mode
 * @param editorNr The editor number
 */
function changeToRunningMode(editorNr){
	// change Icon
	var icon = $("#runButton-" + editorNr);
	changeIcon(editorNr, 'load.gif');
	

	// reset output
	delete errors[editorNr];

	if($("#resultBar-"+editorNr+" div").length != 0){
		// reset tabs
		$("#resultBar-"+editorNr).hide("slow");
		$("#resultBar-"+editorNr+" li, #resultBar-"+editorNr+" .tab-pane").remove();
		// remove text
		$("#bottomBarText-"+editorNr).empty();
	}
	
}

/**
 * Changes the editor with editorNr to completed mode
 * @param editorNr The editor number
 * @param aborted {Boolean} true if the run has been aborted
 */
function changeToCompleted(editorNr, aborted){
	var bottomBarText = $("#bottomBarText-"+editorNr);
	var errorCount = errors[editorNr];
	log("Errors: "+errors[editorNr]+" EditorNr: " + editorNr);
	//hide Text until complete
	bottomBarText.hide();
	$("#resultBar-"+editorNr).hide();

	//remove event handler from run icon
	$("#runButton-"+editorNr).off("click");
	
	//Build output text based on errror count
	if(aborted){
		changeIcon(editorNr, 'error.png');
		bottomBarText.html("<div class=\"alert alert-danger\" role=\"alert\">Something went wrong!</div>");
	} else if(errorCount == 0) {
		changeIcon(editorNr, 'done.png');
		bottomBarText.html("<div class=\"alert alert-success\" role=\"alert\" >Verification successful!</div>");
		
	} else if(errorCount > 0){
		changeIcon(editorNr, 'error.png');
		bottomBarText.html("<div class=\"alert alert-danger\" role=\"alert\">Verification ended with " + errorCount + " error" + ((errorCount > 1)? "s":"") + "!</div>");
		$("#resultBar-"+editorNr).show("slow");
	} else {
		// No infromation about verification errors, probably no result-table
		changeIcon(editorNr, 'done.png');
		bottomBarText.html("<div class=\"alert alert-info\" role=\"alert\" >Verification ended!<div>");
		$("#resultBar-"+editorNr).show("slow");
	}

	if(!aborted) {
		bottomBarText.append("<button type=\"button\" class=\"btn btn-default\">Details</button>");
		//Toggle Details
		$("#bottomBarText-" + editorNr + " button").click(function(){
			$("#resultBar-" + editorNr).toggle("slow");
		});
	}

	//Show text
	bottomBarText.fadeIn("slow");
	
	//Add clicks to return to initial mode
	$("#editor-"+editorNr +", #runButton-" + editorNr).on("click", function(event){
		changeToInitialMode(editorNr);
	});
	
	//Select a tab
	$("#resultBar-"+editorNr+" .nav a:first").tab('show');

}

/**
 * Helper function to change the run icon
 * @param editorNr The editor number
 * @param image The icon file name
 * @returns The icon element
 */
function changeIcon(editorNr, image){
	var icon = $("#runButton-"+editorNr);
	icon.fadeOut("slow", function(){
		icon.attr("src", assetsUrl + "images/" +image);
		icon.fadeIn("slow");
	});
	return icon;
}


/**
 * Adds a tab to the resultBar of the editor specified by editorNr
 * @param editorNr The editor number
 * @param id The id of the result file, as it is received by the server
 * @param label The label of the tab to be displayed to the user
 * @returns The element, which wraps the content of the created tab
 */
function addTab(editorNr, id, label){
	var labels = $("#resultBar-" + editorNr + " ul" );
	var tabs = $("#resultBar-" + editorNr + " .tab-content");
	
	if (id != null) {
		labels.append( "<li role='presentation' class=\"" + (id == 0 ?"active":"")+ "\">"
					+"<a aria-controls='tab"+id+"-"+editorNr+"' role=\"tab\" data-toggle=\"tab\" href='#tab"+id+"-"+editorNr+"'>"+label+"</a></li>");
		tabs.append( "<div role=\"tabpanel\" class=\"tab-pane " + ( id == 0 ?"active":"") + "\" id='tab" + id + "-" + editorNr + "'></div>" );
		return $("#tab"+id+"-"+editorNr);
	} else {
		// Only the run information tab has no id
		var runTab = $("#tab_info-"+editorNr);
		if(runTab.length == 0){
			labels.append( "<li role='presentation'>"
					+"<a aria-controls='tab_info-"+editorNr+"' role=\"tab\" data-toggle=\"tab\" href='#tab_info-"+editorNr+"'>"+label+"</a></li>");
			tabs.append( "<div role=\"tabpanel\" class=\"tab-pane\" id='tab_info-"+editorNr+"'></div>" );
		}
		return $("#tab_info-"+editorNr+"");
	}
}

/**
 * Removes a tab from the Tab list
 * @param editorNr The editor number
 * @param id The id of the result file, as it is received by the server
 */
function removeTab(editorNr, id){
	$("#tab"+id+"-"+editorNr).remove();
	$("a[href='#tab"+id+"-"+editorNr+"']").parent().remove();
}

/**
 * Adds annotations to the Ace code editor specified by editorNr
 * @param editorNr The editor number
 * @param table A JSON encoded object with type "text/table" as it is received from the server
 * @returns The number of added annotations (verification errors)
 */
function setAnnotations(editorNr, table){
	var editor = getEditor(editorNr);
	var annotations = [];
	var tableData = jQuery.parseJSON(table);
	log(tableData);
	$.each(tableData.lines, function(lineNr, line){
		annotations.push({
			row: line.line_nr - 1, //ace counts from 0
			column: line.column_nr,
			text: line.message,
			type: (line.icon == "e" ? "error" : "warning")
		});
	});
	editor.getSession().setAnnotations(annotations);
	return annotations.length
}


/**
 * Renders and displays a selectable table in the given tab.
 * @param tab The tab where the table is displayed
 * @param JSONtable The JSON string containing the table data
 */
function renderTable (editorNr, tab, tableData) {

	var prolog = $("<div class='result_table_prolog'></div>");
	var table = $("<table class='result_table table'></table>");
	var epilog = $("<div class='result_table_epilog'></div>");

	var editor = getEditor(editorNr);
	
	/*if (tableData.prolog != undefined) {
		prolog.html(tableData.prolog)
	}*/
	
	if (tableData.epilog != undefined) {
		epilog.html(tableData.epilog)
	}
	
	if (tableData.lines != undefined) {
		$.each(tableData.lines, function (linenr, line) {
			var row = $("<tr></tr>");
				
			var icon_cell = $("<td></td>");
			if (line.icon == "w") {
				icon_cell.html("<img src='"+assetsUrl+"images/icon_w.png'>");
			} else if (line.icon == "i") {
				icon_cell.html("<img src='"+assetsUrl+"images/icon_i.png'>");
			} else if (line.icon == "e") {
				icon_cell.html("<img src='"+assetsUrl+"images/icon_e.png'>");
			} else if (line.icon == "t") {
				icon_cell.html("<img src='"+assetsUrl+"images/icon_t.png'>");
			}
			
			var coord_cell = $("<td></td>")
			if (line.line_nr != undefined && line.column_nr != undefined) {
				coord_cell.text(line.line_nr+","+line.column_nr);
				row.click(function () {
					editor.focus();
					editor.gotoLine(line.line_nr, line.column_nr-1, true);
				} );
			} else if (line.line_nr != undefined) {
				coord_cell.text(line.line_nr);
				row.click(function () {
					editor.focus();
					editor.gotoLine(line.line_nr, 0, true);
				} );
			}
			
			var message_cell = $("<td></td>");
			if (line.message != undefined) {
				message_cell.text(line.message);
			}
			
			row.append(icon_cell).append(coord_cell).append(message_cell).appendTo(table);
		});
	}
	
	tab.empty();
	prolog.appendTo(tab);
	table.appendTo(tab);
	epilog.appendTo(tab);
}

/**
 * Displays a dialog box containing the permalink for the user to copy.
 * @param editorNr The editor number
 */
function displayPermalink (editorNr) {
	var url = document.URL.split("?");
	
	bootbox.dialog({
		  message: "Copy the following URL to permanently link to the current input and output:<br><p><i>" + url[0] + "?key=" + escapeHTML(getSessionKeyByEditorNr(editorNr)) + "</i></p>",
		  title: "Permalink",
		  buttons: {
		    success: {
		      label: "OK",
		      className: "btn-default"
		  }
		}
	});
}

/**
 * Shows the warning box, including all warnings from the warning list.
 * @param warningList A list of warning messages to be displayed.
 */
function displayWarnings (warningList) {
	if (warningList.length > 0) {
		var warningText = "";
		var title = (warningList.length == 1 ? "Warning" : "Warnings");
		$.each(warningList, function(key, val) {
			warningText = warningText + (val+"<br />");
		});
		bootbox.dialog({
			  message: warningText,
			  title: title,
			  buttons: {
			    success: {
			      label: "OK",
			      className: "btn-default"
			  }
			}
		});
	}
}

/**
 * Displays a dialog box containing an error message.
 * @param title The dialog's title
 * @param message The error message, including details if any.
 */
function displayErrorMessage (title, message) {
	bootbox.dialog({
		  message: message,
		  title: title,
		  buttons: {
		    success: {
		      label: "OK",
		      className: "btn-default"
		  }
		}
	});
}



/* ============= Communication ============== */

/**
 * Sends a run request to the server.
 * Sets the current state to running (deactives the run-button and displays the running-indicator) and starts the polling.
 * @param editorNr The editor number
 */
function runTool(editorNr) {
	if (!running[editorNr]) {
		
		running[editorNr] = true;
		
		//Time measurement (only for one editor on page)
		run_start = Date.now();
		
		var args = {input: editors[editorNr].getValue(), backend: activeBackend[editorNr]};
		$.each(options[editorNr], function(key, val) {
			log(val);
			//remove editor number, otherwise tool doesn't recognize option
			var toolVal = val.slice(0, -4);
			var optionWidget = $("#"+val);
			if (optionWidget.attr("type") == "checkbox") {
				args[toolVal] = optionWidget.is(':checked');
			} else if (new String(optionWidget.prop("tagName")).toLowerCase() == "select") {
				args[toolVal] = $("#"+val+" option:selected").val();
			} else {
				args[toolVal] = optionWidget.val();
			}
		});
		log(args);
		$.ajax({url: serverUrl + "comm/"+tool+"/run",
			type: "POST",
			data: args,
			dataType: "json",
			success: function(runStartInformation) {
				var key = runStartInformation.key
			
				if (key == null) {
					displayErrorMessage(errors.error601.title, errors.error601.message);
					return;
				}
			
				var sessionKey = key;

				addSession(editorNr, sessionKey);
				
				// Start polling for the run-status after 2 seconds.
				setTimeout("pollRunningTool(0, '" + editorNr + "')", 2000);
			},
			error: function(jqXHR) {
				finished(editorNr, false, true);
				if (jqXHR.status == 400 || jqXHR.status == 500) {
					processError(jqXHR.responseText);
				} else {
					displayErrorMessage(errors.error601.title, errors.error601.message);
				}
			}
		});

		// change editor to running mode
		changeToRunningMode(editorNr);

	} else if (getSessionKeyByEditorNr(editorNr) != null) {
		// If the editor is already running, a click on the loading icon triggers an abort
		$.ajax({url: serverUrl + "comm/"+tool+"/abort",
			type: "POST",
			data: {key: getSessionKeyByEditorNr(editorNr)}
		});
	
		finished(editorNr, false, true);
	}
}




/**
 * Sends a poll request to the server, handles the response (displaying errors, warnings and results) and schedules the next request.
 * @param pollCount The current number of poll requests that have been made
 * @param editorNr The editor number
 */
function pollRunningTool (pollCount, editorNr) {
	log("Polling...");
	var sessionKey = getSessionKeyByEditorNr(editorNr);
	log(sessionKey + " " + running[editorNr]);
	if (running[editorNr] && sessionKey != null) {
	$.ajax({url: serverUrl + "comm/"+tool+"/run-status",
		type: "GET",
		data: {key: sessionKey},
		dataType: "json",
		success: function(runStatus) {
		
			if (runStatus == null) {
				displayErrorMessage(errors.error602.title, errors.error602.message);
				return;
			}
		
			// Display output when available
			$.each(runStatus.results.sort(compareResults), function (index, value) {
				displayResult(value.id, value.result_type, value.name, value.modified, editorNr);
			})
			
			// Keep polling until timeout or finished
			if (runStatus.status == "running") {
				setTimeout("pollRunningTool("+(pollCount+1)+", '" + editorNr + "')", getInterval(pollCount));
			} else if (runStatus.status == "timeout") {
				displayErrorMessage("Timeout", "The execution exceeded the timeout and was stopped.");
				finished(editorNr, true, true);
			} else if (runStatus.status == "failed") {
				formatError(runStatus.error);
				finished(editorNr, true, true);
			} else {
				finished(editorNr, true, false);
				displayRunInformation(editorNr, runStatus.duration, runStatus.exit_value);
			}
			
			displayWarnings(runStatus.warnings);
			
		},
		error: function(jqXHR) {
			finished(editorNr, false, true);
			if (jqXHR.status == 400 || jqXHR.status == 500) {
				processError(jqXHR.responseText);
			} else {
				displayErrorMessage(errors.error602.title, errors.error602.message);
			}
		}
		});
	}
}


/**
 * Requests a result from the server and displays the result in the resultBar (adds a new tab if necessary).
 * @param id The result's id. They appear in the order of the ids.
 * @param resultType The result's type, defining how it will be displayed (text, table, jpg, ...)
 * @param label The result's name or label that is displayed on the tab
 * @param modified The result's modified hash value, used to determine if the result has changed since it was last displayed
 * @param editorNr The editor number
 */
function displayResult (id, resultType, label, modified, editorNr) {

	//Check whether tab already exists, create it if not
	var tab = $("#tab"+id+"-"+editorNr);
	log(tab.length);
	if (tab.length == 0) {
		tab = addTab(editorNr, id, label);
	}
	
	var sessionKey = getSessionKeyByEditorNr(editorNr);
	log("Fetch result for session " + sessionKey + " with editorNr["+editorNr+"]");
	
	resultType = resultType.toLowerCase()

	if (modified == undefined || tab.attr("modified") != modified) {
		if (modified != undefined) {
			tab.attr("modified", modified);
		}
		var command = (modified != undefined ? "result" : "logged-result");
		
		if (resultType == "text/plain" || resultType == "text/table") {
			$.ajax({url: serverUrl + "comm/"+tool+"/"+command,
					type: "GET",
					data: {key: sessionKey, result_id: id},
					dataType: "text",
					async: false, 
					success: function(result) {
						if (result == null) {
							if (modified == undefined) {
								displayErrorMessage(errors.error605.title, errors.error605.message);
							} else {
								displayErrorMessage(errors.error603.title, errors.error603.message);
							}
							return;
						}
						
					
						if (resultType == "text/table") {
							var tableData = jQuery.parseJSON(result);
							if(tableData.lines != undefined && tableData.lines.length > 0){
								renderTable(editorNr, tab, tableData);
							} else {
								removeTab(editorNr, id);
							}
							errors[editorNr] = setAnnotations(editorNr, result);
						} else {
							tab.html("<pre>" + escapeHTML(result) + "</pre>");
						}
					},
					error: function(jqXHR) {	
						if (jqXHR.status == 400 || jqXHR.status == 500) {
							processError(jqXHR.responseText);
						} else if (modified == undefined) {
							displayErrorMessage(errors.error605.title, errors.error605.message);
						} else {
							displayErrorMessage(errors.error603.title, errors.error603.message);
							
						}
					}
			});
			
		} else if (resultType == "image/jpeg" || resultType == "image/gif" || resultType == "image/png") {
			tab.html("<img src='" + serverUrl + "comm/"+tool+"/"+command+"?key="+sessionKey+"&amp;result_id="+id+"' class='output_image' alt='"+label+"'>");
		} else if (resultType == "application/pdf") {
			tab.html("<embed src=\"" + serverUrl + "comm/"+tool+"/"+command+"?key="+sessionKey+"&amp;result_id="+id+"\" width=\"100%\" height=\"600px\">");
		} else {
			tab.html("<a href='" + serverUrl + "comm/"+tool+"/"+command+"?key="+sessionKey+"&amp;result_id="+id+"' style='font-weight:bold'>Click here</a> to download the output file.");
		}
	
	}

	
}


/**
 * Adds a tab containing run information
 * @param editorNr The editor number
 * @param duration The running time of the tool in milliseconds
 * @param exitValue The tool's exit value, if any
 * @param date The date the session was executed (applies only to logged sessions)
 * @param version The version number of the tool at the time of the execution
 * @param options The list of options to display, if any
 */
function displayRunInformation (editorNr, duration, exitValue, date, version, options) {
	var runInformation = "<tr><th>Running time:</th><td>"+(duration == undefined ? "N/A" : duration)+" ms</td></tr><tr><th>Exit value:</th><td>"+(exitValue == undefined ? "N/A" : exitValue)+"</td></tr>";
	if (date != undefined) runInformation += "<tr><th>Time of Execution:</th><td>"+escapeHTML(date)+"</td></tr>";
	if (version != undefined) runInformation += "<tr><th>Tool version:</th><td> "+escapeHTML(version)+"</td></tr>"
	
	// Display the options
	runInformation = "<table class=\"table\"><tbody>"+runInformation+"</tbody></table>";
	if (options != undefined && options.length > 0) {
		runInformation += "<h2>Option values</h2><table><tbody>";
		$.each(options, function (key, opt) {
			runInformation += "<tr><th>" + escapeHTML(opt.name) + "</th><td>" + escapeHTML(opt.value) + "</td></tr>";
		});
		runInformation += "</tbody></table>";
	}
	
	addTab(editorNr, null,"Run Information").html(runInformation);
}




/**
 * Is called when a run of the editor specified by editorNr has been finished, either successfull or not
 * @param editorNr The editor number
 * @param allowPermalink Indicates whether a permalink should be made available. Normally true for successful verifications
 * @param aborted Indicates wheter a run has been aborted by the user or an exception happened
 */
function finished (editorNr, allowPermalink, aborted) {
	
	// Change UI
	changeToCompleted(editorNr, aborted);
	running[editorNr] = false;
	
	//ToDo Permalinks
	if(allowPermalink){
		// Show Permalink
    	$("#pinButton-"+editorNr).show();
	}
	
	log((Date.now() - run_start)/1000 + "s");
	
}


/**
 * Restores a logged session (through a permalink), in the specified editor.
 * @param editorNr The editor number
 */
function loadLoggedSession (editorNr) {
	var editor = getEditor(editorNr);
	// Load session if requested (through permalink)
	if (loggedSessionKey != null) {
		$.ajax({url: serverUrl + "comm/"+tool+"/logged-session",
			type: "GET",
			dataType: "json",
			crossDomain: true,
			data: {key: loggedSessionKey},
			success: function(loggedSession) {
				
				editor.session.setValue(loggedSession.input);
				addSession(editorNr, loggedSessionKey);
				log("Added session " + loggedSessionKey);
				
				$.each(loggedSession.results, function (index, value) {
					displayResult(value.id, value.result_type, value.name, value.modified, editorNr);
				});
			
				displayRunInformation(editorNr, loggedSession.duration, loggedSession.exit_value, loggedSession.date, loggedSession.tool_version, loggedSession.options);
				
				finished(editorNr, true, false);
				
				displayWarnings(["The tool may have changed since the time this session was executed. The output displayed below might be outdated. To ensure that the output is up to date, please click the \"Run\" button."]);
				
				
			},
			error: function(jqXHR) {
				if (jqXHR.status == 400 || jqXHR.status == 500) {
					processError(jqXHR.responseText);
				} else {
					displayErrorMessage(errors.error604.title, errors.error604.message);
				}
			}
		});
	}
}



/* ======= Helper function ====== */
/**
 * Generates a human-readable error string from an error object and displays it.
 * @param error The error object
 */
function formatError (error) {
	title = escapeHTML(error.code) + " " + escapeHTML(error.name);
	message = escapeHTML(error.description);
	if (error.details != undefined) {
		message += "<br><br><i>Details</i>:";
			
		$.each(error.details, function (key, val) {
			message += "<br>"+escapeHTML(key) + ": "+escapeHTML(val);
		});
	}
	
	displayErrorMessage(title, message);
}

/**
 * Escapes <, > and & characters to disable the use of HTML markup.
 * @param input The string that is escaped
 */
function escapeHTML (input) {
	return (input+"").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}


/**
 * Returns the number of milliseconds the client should wait before making the next poll request.
 * @param pollCount The current poll count, i.e. how often the client has polled the server already
 */
function getInterval (pollCount) {
	if (pollCount < 10) {
		return 500;
	} else if (pollCount < 20) {
		return 1000;
	} else {
		return 2000;
	}
}



/**
 * Parses a JSON encoded error and displays it int the error dialog.
 * @param errorJsonString The JSON encoded error string
 */
function processError (errorJsonString) {
	var title = null;
	var message = null;

	if (errorJsonString == null) {
		displayErrorMessage(errors.error600.title, errors.error600.message);
	} else {
		formatError(jQuery.parseJSON(errorJsonString));
	}
}

/**
 * compare function to sort the incoming results according to their ID
 * @param a
 * @param b
 * @returns {Number}
 */
function compareResults(a, b) {
	  return a.id - b.id;
}


/**
 * Function to log to the console
 * @param o The object the be logged
 */
function log(o){
	if(logging) console.log(o);
}
