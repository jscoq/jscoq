var PackagesManager;

(function(){

    "use strict";

    PackagesManager = function(panel) {
        this.panel = panel;

        var package_index_url = 'packages-index.json';
        var req = new XMLHttpRequest();
        req.open('GET', package_index_url);
        req.send(null);

        req.addEventListener('readystatechange',
                             () => {
                               if(req.readyState === 4 &&
                                    (req.status === 200 || req.status === 304 || req.status === 0))
                                    this.displayDefinitions(req);
                             });
    };

    PackagesManager.prototype.setup = function() {
        jsCoq.onPkgProgress = (evt) => {
            var ce = new CustomEvent('pkgProgress', {detail:evt});
            document.body.dispatchEvent(ce);
        };
    };

    PackagesManager.prototype.displayDefinitions = function(req) {
        var rows = d3.select(this.panel).selectAll('div')
            .data(JSON.parse(req.responseText))
            .enter()
            .append('div');

        var self = this;
        rows.each(function () {
            var row = d3.select(this);
            row.append('img')
                .attr('src', 'images/dl.png')
                .on('click', () => {self.sendCoqPkg();});

            row.append('span')
                .text(d => d.label);
        });
    };

     PackagesManager.prototype.sendCoqPkg = function() {
         var row = d3.select(d3.event.target.parentNode);
         var dl  = new PackageDowloader(row);
         dl.download();
    };

    var PackageDowloader = function(row) {
        this.row = row;
        this.bar = null;
        this.egg = null;
        this.bundle_name = row.datum().name;
        this.progress = 0; // percent
    };

    PackageDowloader.prototype.download = function() {
        this.row.select('img').on('click', null);
        this.bar = this.row.append('div')
            .attr('class', 'rel-pos')
            .append('div')
            .attr('class', 'progressbar');
        this.egg = this.bar
            .append('img')
            .attr('src', 'images/egg.png')
            .attr('class', 'progress-egg');

        var pkg_json_url = 'coq-pkgs/' + this.bundle_name + '.json';
        var req = new XMLHttpRequest();
        req.open('GET', pkg_json_url);
        req.onreadystatechange = () => {
            if (req.readyState === 4) {
                if (req.status === 200)
                    this._download(JSON.parse(req.responseText));
                // XXX by design we could not access CoqPanel.log
                // TODO: else log error message
            }
        };
        req.send(null);
    };

    PackageDowloader.prototype._download = function(json) {
        var files_total_length = 0;
        var files_loaded_cpt = 0;
        for(var i=0 ; i<json.length ; i++)
            files_total_length += json[i].vo_files.length + json[i].cma_files.length;

        document.body.addEventListener('pkgProgress',
            (evt) => {
                if(evt.detail.bundle_name === this.bundle_name) {
                    this.progress = ++files_loaded_cpt / files_total_length;
                    this.updateProgress();
                    if (files_loaded_cpt === files_total_length)
                        this.finishDownload();
                }
            }
        );
        jsCoq.add_pkg(this.bundle_name);
    };

    PackageDowloader.prototype.updateProgress = function() {
        var angle = (this.progress * 360 * 15) % 360;
        this.egg.style('transform', 'rotate(' + angle + 'deg)');
        this.bar.style('width', this.progress * 100 + '%');
    };

    PackageDowloader.prototype.finishDownload = function() {
        this.row.select('.rel-pos').remove();
        this.row.select('img')
            .attr('src', 'images/checked.png');
    };

}());

// Local Variables:
// js-indent-level: 4
// End:
