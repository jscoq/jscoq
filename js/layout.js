(function () {
    var options = {
        //height: 10,
        cell_height: Math.floor((document.documentElement.clientHeight - 83) / 14),
        //height: 14,
        resizable: {
            handles: 'e, se, s, sw, w'
        },
        vertical_margin: 2,
        handle: '.jscoq-panel-wrapper .caption',
    };
    var grid = $('.grid-stack').gridstack(options);

}());