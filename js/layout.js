"use strict";

class GridLayout {

    constructor(selector) {
        var options = {
            cell_height: Math.floor((document.documentElement.clientHeight - 83) / 14),
            resizable: {
                handles: 'e, se, s, sw, w'
            },
            vertical_margin: 2,
            handle: '.jscoq-panel-wrapper .caption',
        };
        $(selector).gridstack(options);
        $(selector).on('change', (evt, items) => this.save(evt, items));
        this.grid = $(selector).data('gridstack');

        this.presets = {
            Default: {
                "proof": {"x":8,"y":0,"width":4,"height":6},
                "query":{"x":8,"y":6,"width":4,"height":5},
                "packages":{"x":8,"y":11,"width":4,"height":3},
                "document":{"x":0,"y":0,"width":8,"height":14}},
            Projector: {
                "document":{"x":0,"y":0,"width":12,"height":9},
                "query":{"x":8,"y":9,"width":4,"height":5},
                "proof":{"x":0,"y":9,"width":8,"height":5},
                "packages":{"x":0,"y":14,"width":12,"height":1}},
        };
    }

    save(evt, items) {
        var state = {};
        items.map((item) =>
            {
                var name = item.el[0].getAttribute('data-jscoq-name');
                state[name] = {x: item.x,
                              y: item.y,
                              width: item.width,
                              height: item.height};
            }
        )
        console.log(JSON.stringify(state));
    }

    loadPreset(name) {
        var layout = this.presets[name];
        if (!layout) return;
        this.load(layout);
    }

    load(layout) {
        var engine = this.grid.grid;
        engine.nodes.forEach(
            item => {
                var name = item.el[0].getAttribute('data-jscoq-name');
                console.log(name, item);
                this.grid.resize(item.el, 1, 1);
                this.grid.move(item.el, layout[name].x, layout[name].y);
                this.grid.resize(item.el, layout[name].width, layout[name].height);
            }
        )
    }
}
