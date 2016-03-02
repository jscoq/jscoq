(function () {
    var options = {
        //height: 10,
        //cell_height: document.documentElement.clientHeight / 4,
        resizable: {
            handles: 'e, se, s, sw, w'
        },
        vertical_margin: 3,
        //handle: '.jscoq-grid-stack-handle',
    };
    var grid = $('.grid-stack').gridstack(options);

}());