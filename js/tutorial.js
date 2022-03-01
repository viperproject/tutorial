//serverUrl = "http://boogiebox2.inf.ethz.ch:1001/viperonline/";
serverUrl = "http://viper.ethz.ch/viperonline/";
assetsUrl = "http://viper.ethz.ch/tutorial/";
tool = "silver";
language = "silver";

$(document).ready(() => {
  $(".load-code").each(function(index) {
    let editorNr = 100 + index;
    let editorId = `editor-${editorNr}`;
    let button = $(this);
    button.click(() => {
      let codeBlock = button.parent().parent();
      let code = codeBlock.text();

      codeBlock.after(`<div id="${editorId}"></div>`);
      codeBlock.remove();

      console.log("start", editorId, codeBlock);

      let editor = ace.edit(editorId);
      editor.setTheme("ace/theme/textmate");
      editor.getSession().setMode("ace/mode/silver");
      editor.setOptions({
        maxLines: 25,
        minLines: 25,
        fontFamily: "Lucida Console, monospace",
        fontSize: "12pt",
      });
      editor.setShowPrintMargin(false);
      editor.getSession().setUseWorker(false);
      editor.getSession().setValue(code);

      addEditor(editorNr, editor);
      $("#" + editorId).wrap(`<div id='container-${editorNr}' class='editorContainer'></div>`);
      buildGUI(editorNr);

      // add spacer
      $(`#resultBar-${editorNr}`).after(`<div style="height: 50px;"></div>`);
    });
  });
});
