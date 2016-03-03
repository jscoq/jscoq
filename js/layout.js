(function () {
    var options = {
        //height: 10,
        cell_height: Math.floor(document.documentElement.clientHeight / 15),
        resizable: {
            handles: 'e, se, s, sw, w'
        },
        vertical_margin: 2,
        //handle: '.jscoq-grid-stack-handle',
    };
    var grid = $('.grid-stack').gridstack(options);

}());